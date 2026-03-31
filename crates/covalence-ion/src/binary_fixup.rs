/// Post-processing fixup for Ion 1.0 binary output from `ion-rs` on `wasm32`.
///
/// # Upstream bug
///
/// `ion-rs` 1.0.0-rc.11 has a bug in `VarUInt::encoded_size_of`
/// (`src/binary/var_uint.rs`, line 38):
///
/// ```text
/// let bits_used = usize::BITS as usize - leading_zeros;
///                 ^^^^^^^^^^
/// ```
///
/// The input `value` is a `u64`, so `leading_zeros()` returns a count out of 64 bits.
/// But `usize::BITS` is only 32 on wasm32, causing `32 - 58 = underflow` for typical
/// annotation wrapper lengths.  The fix is to change `usize::BITS` to `u64::BITS`.
///
/// `encoded_size_of` is called in
/// `lazy/encoder/binary/v1_0/container_writers.rs:120` to pre-compute the
/// container header length for annotation wrappers.  The wrong value propagates to
/// `envelope_length`, which is then VarUInt-encoded as the annotation wrapper's
/// declared length — producing a multi-byte VarUInt encoding a garbage value
/// instead of the correct 1-byte encoding.
///
/// The actual *content* bytes (annotations, struct body, field values) are all
/// written correctly — only the annotation wrapper VarUInt length is wrong.
///
/// # What this module does
///
/// [`fixup_binary_ion`] rewrites a binary Ion 1.0 stream, recursively visiting
/// every container and annotation wrapper and recomputing lengths from the
/// actual content bytes.  On correct (non-buggy) input this is a no-op.

const ION_1_0_IVM: [u8; 4] = [0xE0, 0x01, 0x00, 0xEA];

// Ion 1.0 binary type codes
const TYPE_BOOL: u8 = 1;
const TYPE_LIST: u8 = 0xB;
const TYPE_SEXP: u8 = 0xC;
const TYPE_STRUCT: u8 = 0xD;
const TYPE_ANNOTATION: u8 = 0xE;

/// Read a VarUInt starting at `data[0]`. Returns `(value, bytes_consumed)`.
fn read_varuint(data: &[u8]) -> (usize, usize) {
    let mut value: usize = 0;
    for (i, &byte) in data.iter().enumerate() {
        value = (value << 7) | (byte & 0x7F) as usize;
        if byte & 0x80 != 0 {
            return (value, i + 1);
        }
    }
    // Reached end of data without stop bit — return what we have
    (value, data.len())
}

/// Write a VarUInt value to `out`.
fn write_varuint(out: &mut Vec<u8>, value: usize) {
    if value == 0 {
        out.push(0x80);
        return;
    }

    // Encode into a small buffer right-to-left
    let mut buf = [0u8; 10];
    let mut v = value;
    let mut pos = buf.len();
    let mut first = true;
    while v > 0 || first {
        pos -= 1;
        buf[pos] = (v & 0x7F) as u8;
        if first {
            buf[pos] |= 0x80; // Set stop bit on the last (rightmost) byte
            first = false;
        }
        v >>= 7;
    }
    out.extend_from_slice(&buf[pos..]);
}

/// Compute the total byte length of a value at `data[0]` (header + body).
///
/// Uses the declared lengths, which are correct for everything except annotation
/// wrapper lengths (the only thing affected by the bug).  This function is only
/// called on values we are copying verbatim.
fn value_byte_length(data: &[u8]) -> usize {
    if data.is_empty() {
        return 0;
    }
    let td = data[0];
    let type_code = td >> 4;
    let nibble = td & 0x0F;

    // NOP padding (0x00) or null.null (0x0F) — also bool (type 1) has value in nibble
    if (type_code == 0 && nibble == 0) || nibble == 0x0F || type_code == TYPE_BOOL {
        return 1;
    }

    if nibble <= 0x0D {
        return 1 + nibble as usize;
    }

    // nibble == 0x0E: VarUInt-encoded length follows
    if data.len() < 2 {
        return data.len();
    }
    let (length, varuint_size) = read_varuint(&data[1..]);
    1 + varuint_size + length
}

/// Fix a single value starting at `input[pos]`, appending corrected bytes to `output`.
/// Returns the position in `input` after this value.
fn fixup_value(input: &[u8], pos: usize, output: &mut Vec<u8>) -> usize {
    if pos >= input.len() {
        return pos;
    }
    let td = input[pos];
    let type_code = td >> 4;
    let nibble = td & 0x0F;

    // Annotation wrapper with VarUInt length — the potentially buggy case
    if type_code == TYPE_ANNOTATION && nibble == 0x0E {
        return fixup_annotation_wrapper(input, pos, output);
    }

    // Containers (list, sexp, struct) that might contain nested annotation wrappers
    let is_container = type_code == TYPE_LIST || type_code == TYPE_SEXP || type_code == TYPE_STRUCT;
    if is_container && nibble != 0x0F {
        return fixup_container(input, pos, output);
    }

    // Scalar, null, bool, inline-length annotation wrapper — copy verbatim
    let len = value_byte_length(&input[pos..]);
    let end = (pos + len).min(input.len());
    output.extend_from_slice(&input[pos..end]);
    end
}

/// Fix an annotation wrapper starting at `input[pos]` (byte = 0xEE).
fn fixup_annotation_wrapper(input: &[u8], pos: usize, output: &mut Vec<u8>) -> usize {
    // Skip past 0xEE
    let mut rpos = pos + 1;

    // Read the (possibly wrong) VarUInt length to find where content starts
    let (_bad_length, bad_varuint_size) = read_varuint(&input[rpos..]);
    rpos += bad_varuint_size;
    let content_start = rpos;

    // Read annot_length VarUInt (correct)
    let (annot_length, annot_length_size) = read_varuint(&input[rpos..]);
    rpos += annot_length_size;
    rpos += annot_length; // Skip past annotations

    // Recursively fix the wrapped value (it's a single value)
    let mut fixed_content = Vec::new();
    // Copy the annot_length VarUInt + annotation bytes as-is (they are correct)
    fixed_content.extend_from_slice(&input[content_start..rpos]);
    // Fix the wrapped value
    let wrapped_end = fixup_value(input, rpos, &mut fixed_content);

    // Write the corrected annotation wrapper
    let correct_length = fixed_content.len();
    if correct_length <= 0x0D {
        output.push(0xE0 | correct_length as u8);
    } else {
        output.push(0xEE);
        write_varuint(output, correct_length);
    }
    output.extend_from_slice(&fixed_content);

    wrapped_end
}

/// Fix a container (list, sexp, struct) starting at `input[pos]`.
fn fixup_container(input: &[u8], pos: usize, output: &mut Vec<u8>) -> usize {
    let td = input[pos];
    let type_code = td >> 4;
    let nibble = td & 0x0F;

    let (body_length, header_size) = if nibble == 0 {
        (0, 1)
    } else if nibble <= 0x0D {
        (nibble as usize, 1)
    } else {
        // nibble == 0x0E: VarUInt length follows
        let (len, vs) = read_varuint(&input[pos + 1..]);
        (len, 1 + vs)
    };

    let body_start = pos + header_size;
    let body_end = (body_start + body_length).min(input.len());

    // Recursively fix the container's body
    let mut fixed_body = Vec::new();
    let mut bpos = body_start;

    if type_code == TYPE_STRUCT {
        // Struct fields: VarUInt field_name_sid followed by a value
        while bpos < body_end {
            // Copy the field name SID VarUInt
            let (_, field_name_size) = read_varuint(&input[bpos..]);
            fixed_body.extend_from_slice(&input[bpos..bpos + field_name_size]);
            bpos += field_name_size;
            // Fix the field value
            bpos = fixup_value(input, bpos, &mut fixed_body);
        }
    } else {
        // List or sexp: just values
        while bpos < body_end {
            bpos = fixup_value(input, bpos, &mut fixed_body);
        }
    }

    // Write the fixed container header
    let fixed_len = fixed_body.len();
    if fixed_len == 0 {
        output.push(type_code << 4);
    } else if fixed_len <= 0x0D {
        output.push((type_code << 4) | fixed_len as u8);
    } else {
        output.push((type_code << 4) | 0x0E);
        write_varuint(output, fixed_len);
    }
    output.extend_from_slice(&fixed_body);

    body_end
}

/// Fix annotation wrapper VarUInt lengths in an Ion 1.0 binary stream.
///
/// Works around a bug in `ion-rs` 1.0.0-rc.11 where `VarUInt::encoded_size_of` uses
/// `usize::BITS` instead of `u64::BITS`, producing incorrect annotation wrapper lengths
/// on wasm32 targets.  See module-level docs for details.
///
/// On correct (non-buggy) input this is a no-op: the rewritten bytes are identical.
pub fn fixup_binary_ion(input: &[u8]) -> Vec<u8> {
    // Must start with the Ion 1.0 IVM
    if input.len() < 4 || input[0..4] != ION_1_0_IVM {
        return input.to_vec();
    }

    let mut output = Vec::with_capacity(input.len());
    output.extend_from_slice(&ION_1_0_IVM);

    let mut pos = 4;
    while pos < input.len() {
        let new_pos = fixup_value(input, pos, &mut output);
        if new_pos <= pos {
            // Safety: copy remaining bytes verbatim to avoid infinite loop
            output.extend_from_slice(&input[pos..]);
            break;
        }
        pos = new_pos;
    }

    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn noop_on_correct_binary() {
        use crate::ion_rs::{Element, v1_0::Binary};

        let text = r#"{ name: "hello", value: 42, tags: ["a", "b", "c"], nested: { x: 1, y: 2 } }
null.struct
('+' 1 2)
[true, false, null]"#;
        let seq = Element::read_all(text.as_bytes()).unwrap();
        let bytes = seq.encode_as(Binary).unwrap();

        let fixed = fixup_binary_ion(&bytes);
        assert_eq!(bytes, fixed, "fixup should be a no-op on correct binary");
    }

    #[test]
    fn fixes_bad_annotation_wrapper_varuint() {
        // Simulated bad binary: correct content but with a wrong annotation wrapper VarUInt.
        // We construct this by taking good binary and expanding the VarUInt at byte 5
        // to match what the wasm32 bug produces (value 613566786 → 5-byte VarUInt).
        use crate::ion_rs::{Element, v1_0::Binary};

        let text = r#"{ name: "hello", value: 42, tags: ["a", "b", "c"], nested: { x: 1, y: 2 } }
null.struct
('+' 1 2)
[true, false, null]"#;
        let seq = Element::read_all(text.as_bytes()).unwrap();
        let good_bytes = seq.encode_as(Binary).unwrap();

        Element::read_all(&good_bytes).expect("good bytes should decode");

        assert_eq!(good_bytes[4], 0xEE, "annotation wrapper marker");
        let (_correct_length, varuint_size) = read_varuint(&good_bytes[5..]);
        assert_eq!(varuint_size, 1, "correct VarUInt should be 1 byte");

        // Create a bad VarUInt (5 bytes) encoding the bogus value the wasm32 bug produces
        let bogus_length = 613566786usize;
        let mut bad_varuint = Vec::new();
        write_varuint(&mut bad_varuint, bogus_length);
        assert_eq!(bad_varuint.len(), 5, "bogus VarUInt should be 5 bytes");

        let mut bad_bytes = Vec::new();
        bad_bytes.extend_from_slice(&good_bytes[0..5]); // IVM + 0xEE
        bad_bytes.extend_from_slice(&bad_varuint); // Wrong VarUInt
        bad_bytes.extend_from_slice(&good_bytes[5 + varuint_size..]); // Rest of content

        assert!(
            Element::read_all(&bad_bytes).is_err(),
            "bad bytes should fail to decode"
        );

        let fixed = fixup_binary_ion(&bad_bytes);

        let decoded = Element::read_all(&fixed).expect("fixed bytes should decode");
        assert_eq!(seq, decoded, "decoded data should match original");
    }

    #[test]
    fn fixes_nested_annotated_container() {
        use crate::ion_rs::{Element, v1_0::Binary};

        let text = r#"foo::{a:1,b:2,c:3,d:4,e:5,f:6,g:7,h:8,i:9,j:10,k:11,l:12,m:13}"#;
        let seq = Element::read_all(text.as_bytes()).unwrap();
        let good_bytes = seq.encode_as(Binary).unwrap();

        let decoded = Element::read_all(&good_bytes).unwrap();
        assert_eq!(seq, decoded);

        let fixed = fixup_binary_ion(&good_bytes);
        let decoded2 = Element::read_all(&fixed).unwrap();
        assert_eq!(seq, decoded2);
    }

    #[test]
    fn read_write_varuint_roundtrip() {
        for value in [0, 1, 34, 127, 128, 255, 1000, 65535, 613566786] {
            let mut buf = Vec::new();
            write_varuint(&mut buf, value);
            let (decoded, size) = read_varuint(&buf);
            assert_eq!(decoded, value, "value {value}");
            assert_eq!(size, buf.len(), "size for value {value}");
        }
    }
}
