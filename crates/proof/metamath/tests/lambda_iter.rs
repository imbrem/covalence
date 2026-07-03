//! Shallow embedding of `λ_iter` (the first-order expression language with
//! branching and iteration from §2.1 of "Categorical Imperative Programming")
//! as a hand-encoded Metamath theory, checked by the same RPN/DV/substitution
//! engine as set.mm.
//!
//! This is the *shallow* route: the object grammar (Fig 1) becomes Metamath
//! syntax axioms, and each typing / subtyping / weakening rule (Fig 2) becomes
//! an `$a`. A `λ_iter` typing derivation is then literally a Metamath proof,
//! checked for free. Object variables are a syntactic class `vr`; binders carry
//! `$d` freshness side-conditions standing in for the grammar's `x ∉ Γ`.
//!
//! What this does NOT do (by design): the metatheory (weakening-admissibility
//! 2.1.1.2.1, substitution 2.1.1.2.2) is not statable here — those quantify over
//! all derivations and need induction over the typing relation, which a shallow
//! embedding gives no handle on. They belong in a deep embedding / the HOL layer.

use covalence_metamath::{parse, verify_all};

/// The `λ_iter` signature: syntax (Fig 1) + pure typing rules (Fig 2).
const LAMBDA_ITER: &str = r#"
    $( ----------------------------------------------------------------- $)
    $(  Typecodes and metavariables                                      $)
    $( ----------------------------------------------------------------- $)
    $c ty ex ctx vr ins |- $.            $( typecode constants            $)
    $c 0 1 ox o+ ( ) $.                  $( type / grouping constructors  $)
    $c <> , inl inr let = ; case iter abort { } il ir $. $( expr ctors    $)
    $c |= : <: [= isig leb $.            $( judgement constants           $)
    $c [] $.                             $( empty context                 $)

    $v A B C Ap Bp $.
    $v a b c e $.
    $v f $.
    $v x y $.
    $v G H $.

    tA  $f ty A $.
    tB  $f ty B $.
    tC  $f ty C $.
    tAp $f ty Ap $.
    tBp $f ty Bp $.
    ea  $f ex a $.
    eb  $f ex b $.
    ec  $f ex c $.
    ee  $f ex e $.
    nf  $f ins f $.
    vx  $f vr x $.
    vy  $f vr y $.
    cG  $f ctx G $.
    cH  $f ctx H $.

    $( ----------------------------------------------------------------- $)
    $(  Types (Fig 1):  A, B ::= X | A (x) B | 1 | A + B | 0             $)
    $( ----------------------------------------------------------------- $)
    ty0  $a ty 0 $.
    ty1  $a ty 1 $.
    tyox $a ty ( A ox B ) $.
    tyoo $a ty ( A o+ B ) $.

    $( ----------------------------------------------------------------- $)
    $(  Expressions (Fig 1)                                              $)
    $( ----------------------------------------------------------------- $)
    exv   $a ex x $.                              $( variable as expr      $)
    exun  $a ex <> $.                             $( unit value ()         $)
    expr  $a ex ( a , b ) $.                       $( pair                  $)
    exop  $a ex ( f a ) $.                         $( instruction app f a   $)
    exinl $a ex ( inl a ) $.
    exinr $a ex ( inr a ) $.
    exab  $a ex ( abort a ) $.
    exlet $a ex ( let x = a ; b ) $.
    exlp  $a ex ( let ( x , y ) = a ; b ) $.
    exca  $a ex ( case e { il x : a ; ir y : b } ) $.
    exit  $a ex ( iter a { ir x : b } ) $.

    $( ----------------------------------------------------------------- $)
    $(  Contexts (Fig 1):  G ::= [] | G , x : A                          $)
    $( ----------------------------------------------------------------- $)
    cnil  $a ctx [] $.
    ccons $a ctx ( G , x : A ) $.

    $( ----------------------------------------------------------------- $)
    $(  Subtyping  A <: B   (Fig 2)                                      $)
    $(  base order `leb` left abstract: parametric over the base poset X $)
    $( ----------------------------------------------------------------- $)
    ${
      sbase.h $e |- A leb B $.
      sbase   $a |- A <: B $.
    $}
    ${
      sox.l $e |- A <: Ap $.
      sox.r $e |- B <: Bp $.
      sox   $a |- ( A ox B ) <: ( Ap ox Bp ) $.
    $}
    ${
      soo.l $e |- A <: Ap $.
      soo.r $e |- B <: Bp $.
      soo   $a |- ( A o+ B ) <: ( Ap o+ Bp ) $.
    $}
    sinit $a |- 0 <: A $.                          $( 0 initial            $)
    sterm $a |- A <: 1 $.                          $( 1 terminal           $)

    $( ----------------------------------------------------------------- $)
    $(  Context weakening  G [= H   (Fig 2)                              $)
    $( ----------------------------------------------------------------- $)
    wnil $a |- [] [= [] $.
    ${
      wcons.w $e |- G [= H $.
      wcons.s $e |- A <: B $.
      wcons   $a |- ( G , x : A ) [= ( H , x : B ) $.
    $}
    ${
      $d x H $.
      wdrop.w $e |- G [= H $.
      wdrop   $a |- ( G , x : A ) [= H $.
    $}

    $( ----------------------------------------------------------------- $)
    $(  Instruction signatures  f : A -> B   (fixed signature `isig`)    $)
    $( ----------------------------------------------------------------- $)
    $( instruction sigs are added per-instance as axioms, e.g.
       `c0sig $a |- isig c0 1 ( 1 o+ 1 ) $.`                             $)

    $( ----------------------------------------------------------------- $)
    $(  Typing  G |= a : A   (Fig 2)                                     $)
    $( ----------------------------------------------------------------- $)
    ${
      var.w $e |- G [= ( [] , x : A ) $.
      var   $a |- G |= x : A $.
    $}
    ${
      op.s $e |- isig f A B $.
      op.a $e |- G |= a : A $.
      op   $a |- G |= ( f a ) : B $.
    $}
    ${
      $d x G $.
      let.a $e |- G |= a : A $.
      let.b $e |- ( G , x : A ) |= b : B $.
      let   $a |- G |= ( let x = a ; b ) : B $.
    $}
    tunit $a |- G |= <> : 1 $.
    ${
      pair.a $e |- G |= a : A $.
      pair.b $e |- G |= b : B $.
      pair   $a |- G |= ( a , b ) : ( A ox B ) $.
    $}
    ${
      $d x G $. $d y G $. $d x y $.
      lp.a $e |- G |= a : ( A ox B ) $.
      lp.c $e |- ( ( G , x : A ) , y : B ) |= c : C $.
      letpair $a |- G |= ( let ( x , y ) = a ; c ) : C $.
    $}
    ${
      inl.a $e |- G |= a : A $.
      inl   $a |- G |= ( inl a ) : ( A o+ B ) $.
    $}
    ${
      inr.b $e |- G |= b : B $.
      inr   $a |- G |= ( inr b ) : ( A o+ B ) $.
    $}
    ${
      abort.a $e |- G |= a : 0 $.
      abort   $a |- G |= ( abort a ) : C $.
    $}
    ${
      $d x G $. $d y G $.
      case.e $e |- G |= e : ( A o+ B ) $.
      case.a $e |- ( G , x : A ) |= a : C $.
      case.b $e |- ( G , y : B ) |= b : C $.
      case   $a |- G |= ( case e { il x : a ; ir y : b } ) : C $.
    $}
    ${
      $d x G $.
      iter.a $e |- G |= a : A $.
      iter.b $e |- ( G , x : A ) |= b : ( B o+ A ) $.
      iter   $a |- G |= ( iter a { ir x : b } ) : B $.
    $}
"#;

#[test]
fn lambda_iter_signature_parses() {
    let db = parse(LAMBDA_ITER).unwrap();
    assert_eq!(verify_all(&db).unwrap(), 0); // axioms only, no $p yet
    assert!(db.statement_by_label("iter").is_some());
    assert!(db.statement_by_label("let").is_some());
}

#[test]
fn lambda_iter_typecheck_let() {
    // Derivation of:   []  |=  ( let x = <> ; x )  :  1
    //
    //   tunit                         : [] |= <> : 1
    //   wnil, sterm[A:=1] -> wcons    : ( [] , x : 1 ) [= ( [] , x : 1 )
    //   var                           : ( [] , x : 1 ) |= x : 1
    //   let                           : [] |= ( let x = <> ; x ) : 1
    let src = format!(
        "{LAMBDA_ITER}
        thlet $p |- [] |= ( let x = <> ; x ) : 1 $=
          ty1 ty1 exun vx exv vx cnil      $( let floats: A:=1 B:=1 a:=<> b:=x x:=x G:=[] $)
          cnil tunit                       $( let.a:  [] |= <> : 1                          $)
          ty1 vx ty1 vx cnil ccons         $( var floats: A:=1 x:=x G:=( [] , x : 1 )       $)
            ty1 ty1 vx cnil cnil wnil ty1 sterm wcons  $( var.w: (..) [= (..) by wcons      $)
          var                              $( let.b:  ( [] , x : 1 ) |= x : 1               $)
          let $.
        "
    );
    let db = parse(&src).unwrap();
    match verify_all(&db) {
        Ok(n) => assert_eq!(n, 1),
        Err(e) => panic!("thlet failed: {e}"),
    }
}

#[test]
fn lambda_iter_typecheck_iter() {
    // Derivation of:   []  |=  ( iter <> { ir x : ( inl x ) } )  :  1
    //
    // The loop starts at () : 1 and its body re-binds x : 1, immediately exiting
    // with `inl x : 1 + 1` (a `B + A` body with B = A = 1), so the loop has
    // type B = 1. Exercises `iter` + `inl` + `var` under the loop binder.
    let src = format!(
        "{LAMBDA_ITER}
        thiter $p |- [] |= ( iter <> {{ ir x : ( inl x ) }} ) : 1 $=
          ty1 ty1 exun  vx exv exinl  vx cnil   $( iter floats: A:=1 B:=1 a:=<> b:=(inl x) $)
          cnil tunit                            $( iter.a:  [] |= <> : 1                    $)
          ty1 ty1 vx exv  ty1 vx cnil ccons     $( inl floats: A:=1 B:=1 a:=x G:=( [],x:1 ) $)
            ty1 vx ty1 vx cnil ccons            $( var floats                              $)
              ty1 ty1 vx cnil cnil wnil ty1 sterm wcons
            var                                 $( inl.a:  ( [],x:1 ) |= x : 1             $)
          inl                                   $( iter.b: ( [],x:1 ) |= ( inl x ):( 1+1 ) $)
          iter $.
        "
    );
    let db = parse(&src).unwrap();
    match verify_all(&db) {
        Ok(n) => assert_eq!(n, 1),
        Err(e) => panic!("thiter failed: {e}"),
    }
}

#[test]
fn lambda_iter_ill_typed_rejected() {
    // `<>` has type 1, not 0, so `abort <>` must NOT typecheck: feeding the
    // unit value where `abort` demands a `: 0` premise is rejected by the engine.
    let src = format!(
        "{LAMBDA_ITER}
        bad $p |- [] |= ( abort <> ) : 1 $=
          ty1 cnil exun  cnil tunit  abort $.
        "
    );
    let db = parse(&src).unwrap();
    assert!(
        verify_all(&db).is_err(),
        "abort <> : 1 should be rejected (<> : 1, but abort needs : 0)"
    );
}
