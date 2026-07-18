;; nat.sig — the CANONICAL `nat` SIGNATURE (surface-compiler §3.0): the
;; interface/vocabulary the full nat theory (`init/nat.thy`) is stated over. One
;; sort `nat` (the carrier; for the self model it IS kernel `nat`) and every
;; operation the specs mention: the recursor `rec`, the constructors `zero`/`succ`,
;; arithmetic `add`/`mul`/`sub`/`pow`/`shl`, and the order relations `le`/`lt`.
;;
;; This `.sig` is a `(#sig …)` body — single-sorted, first-order. The op symbols
;; are named exactly as the kernel-nat interpretation uses them (`add` is the
;; signature name; the self model interprets it as `nat.add`), so the witnessing
;; model is the IDENTITY on kernel nat. A generic, carrier-abstract presentation
;; (specs over a `tfree` sort, re-elaborated at any structure carrying a `natrec`)
;; is deferred — see the generated open-work index.
(#sig nat
  (sort nat)
  ;; the recursor — `natRec z f n` (natrec-op specialized at the sort)
  (op rec  (-> nat (-> nat nat nat) nat nat))
  ;; constructors
  (op zero nat)
  (op succ (-> nat nat))
  ;; arithmetic
  (op add  (-> nat nat nat))
  (op mul  (-> nat nat nat))
  (op sub  (-> nat nat nat))
  (op pow  (-> nat nat nat))
  (op shl  (-> nat nat nat))
  ;; order
  (op le   (-> nat nat bool))
  (op lt   (-> nat nat bool)))
