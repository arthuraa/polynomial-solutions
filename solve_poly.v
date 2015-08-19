(* Solutions of a quadratic equation over the algebraic numbers *)

Require Import Ssreflect.ssreflect Ssreflect.ssrfun Ssreflect.ssrbool.
Require Import Ssreflect.ssrnat Ssreflect.eqtype Ssreflect.seq.
Require Import Ssreflect.fintype.

Require Import MathComp.bigop MathComp.ssralg MathComp.ssrnum.
Require Import MathComp.algC MathComp.poly.
Require Import MathComp.cyclotomic MathComp.binomial.

Require Import ssrring.

Section Roots.

Local Open Scope ring_scope.

Section Quadratic.

Variables a b c : algC.

Lemma quadratic x :
  a != 0 ->
  let D := b ^+ 2 - 4%:R * a * c in
  (a * x ^+ 2 + b * x + c == 0) =
  (x \in [:: (-b + sqrtC D) / (2%:R * a);
             (-b - sqrtC D) / (2%:R * a)]).
Proof.
move=> an0 D.
rewrite (can2_eq (GRing.addrK c) (GRing.subrK c)) GRing.add0r.
rewrite -(inj_eq (GRing.mulfI (_ : 4%:R * a != 0))); last first.
  by rewrite GRing.mulf_eq0 -[0]/(0%:R) eqC_nat.
rewrite GRing.mulrN GRing.mulrDr (GRing.mulrC b).
rewrite -[4 in X in X == _]/((2 * 2)%N) [in X in X == _]GRing.natrM.
rewrite GRing.mulrA -[_ * a * a]GRing.mulrA -(GRing.expr2 a).
rewrite -{1}(GRing.expr2 2%:R) -GRing.exprMn_comm; last exact: GRing.mulrC.
rewrite -GRing.exprMn_comm; last exact: GRing.mulrC.
rewrite -[_ * _ * a]GRing.mulrA -[_ * _ * (x * b)]GRing.mulrA.
rewrite [2%:R * (_ * _)]GRing.mulr_natl GRing.mulrA.
rewrite -(inj_eq (GRing.addIr (b ^+ 2))) -GRing.sqrrD.
rewrite [_ + b ^+ _]GRing.addrC -[b ^+ _ + _]/D -[D in LHS]sqrtCK GRing.eqf_sqr.
rewrite !(can2_eq (GRing.addrK b) (GRing.subrK b)) ![_ - b]GRing.addrC.
have e : 2%:R * a != 0 by rewrite GRing.mulf_eq0 -[0]/(0%:R) eqC_nat.
by rewrite !(can2_eq (GRing.mulKf e) (GRing.mulVKf e)) ![_^-1 * _]GRing.mulrC !inE.
Qed.

End Quadratic.

Section Cubic.

Lemma eqCn0 (n : nat) : (n%:R == 0 :> algC) = (n == 0%N).
Proof. by rewrite -[0]/0%:R eqC_nat. Qed.

Ltac solve_neq0 :=
  repeat match goal with
  | |- context[_ * _ == 0] =>
    rewrite GRing.mulf_eq0 //=
  | |- context[_%:R == 0] =>
    rewrite eqCn0 //=
  | |- context[_ ^+ _ == 0] =>
    rewrite GRing.expf_eq0 //=
  | |- context[_ ^-1 == 0] =>
    rewrite GRing.invr_eq0 //=
  | |- context[- _ == 0] =>
    rewrite GRing.oppr_eq0 //=
  end.

Lemma cubic (a b c d x : algC) :
  a != 0 ->
  let y := b / (3%:R * a) in
  let p := (3%:R * a * c - b ^+ 2)
           / (3%:R * a ^+ 2) in
  let q := (2%:R * b ^+ 3 - 9%:R * a * b * c + 27%:R * a ^+ 2 * d)
           / (27%:R * a ^+ 3) in
  let u := 3.-root (- q / 2%:R + sqrtC (q ^+ 2 / 4%:R + p ^+ 3 / 27%:R)) in
  let s := val (C_prim_root_exists (erefl (0 < 3)%N)) in
  (a * x ^+ 3 + b * x ^+ 2 + c * x + d == 0) =
  [exists i : 'I_3,
     x == (if p == 0 then - y + s ^+ i * 3.-root (- q)
           else - y + (s ^+ i * u - p / (3%:R * s ^+ i * u)))].
Proof.
move=> an0 y p q u s.
move: s (valP _ : 3.-primitive_root s) => s prim_s.
have ->: a * x ^+ 3 + b * x ^+ 2 + c * x + d =
         a * ((x + y) ^+ 3 + p * (x + y) + q).
  by rewrite /y /p /q; ssfield; solve_neq0.
rewrite (can2_eq (GRing.mulKf an0) (GRing.mulVKf an0)) GRing.mulr0.
rewrite -{3}(GRing.addrK y x).
transitivity [exists i : 'I_3,
                x + y == (if p == 0 then s ^+ i * 3.-root (- q)
                          else s ^+ i * u - p / (3%:R * s ^+ i * u))]; last first.
  apply: eq_existsb=> i.
  rewrite [in RHS]fun_if [_ - y]GRing.addrC !(inj_eq (GRing.addrI _)).
  by rewrite -fun_if.
move: (x + y) p q @u => {x y a b c d an0} x p q u.
have [-> {p u}|pn0] := altP (p =P 0).
  rewrite GRing.mul0r GRing.addr0 (can2_eq (GRing.addrK q) (GRing.subrK q)).
  rewrite GRing.add0r -[X in _ == X](rootCK (erefl (0 < 3)%N)).
  move: (3.-root _)=> {q} q.
  have [->{q}|qn0] := altP (q =P 0).
    rewrite GRing.expr0n /= GRing.expf_eq0 /=.
    apply/eqP/existsP=> [->|[? /eqP ->]]; first exists ord0;
    by rewrite ?GRing.mulr0.
  have q3n0 : q ^+ 3 != 0 by exact: GRing.expf_neq0.
  transitivity [exists i : 'I_3, x / q == s ^+ i]; last first.
    apply: eq_existsb=> i.
    by rewrite (can2_eq (GRing.mulfVK qn0) (GRing.mulfK qn0)).
  rewrite -(GRing.mul1r (q ^+ 3)).
  rewrite -(can2_eq (GRing.mulfVK q3n0) (GRing.mulfK q3n0)).
  rewrite -GRing.expr_div_n.
  apply/eqP/existsP; first by move/(prim_rootP prim_s)=> [i ->]; eauto.
  case=> [i /eqP ->].
  by rewrite GRing.exprAC (prim_expr_order prim_s) GRing.expr1n.
apply/eqP/existsP.
  have [v vn0 -> {x}]: exists2 v, v != 0 & x = v - p / (3%:R * v).
    pose v := (x + sqrtC (x ^+ 2 + 4%:R * p / 3%:R)) / 2%:R.
    have := quadratic 1 (- x) (- p / 3%:R) v (GRing.oner_neq0 _).
    rewrite /= GRing.mul1r inE GRing.opprK GRing.sqrrN !GRing.mulr1.
    rewrite GRing.mulrA [in RHS]/v GRing.mulrN !GRing.mulNr GRing.opprK eqxx.
    move: v => v /=; have [->|vn0] := eqVneq v 0.
      rewrite GRing.expr0n GRing.mulr0 /= GRing.add0r GRing.addrC GRing.subr0.
      rewrite GRing.oppr_eq0 GRing.mulf_eq0 (negbTE pn0) /= GRing.invr_eq0.
      by rewrite eqCn0.
    move=> /eqP Pv; exists v=> //.
    apply: (GRing.mulIf vn0).
    apply: (GRing.addIr (- (x * v))).
    rewrite GRing.subrr -Pv.
    ssfield; solve_neq0.
  set v' := - (p / (3%:R * v)).
  have ->: (v + v') ^+ 3 = v ^+ 3 + v' ^+ 3 + 3%:R * v * v' * (v + v').
    by ssring.
  have ->: 3%:R * v * v' = - p.
    rewrite /v' GRing.mulrC GRing.mulNr; apply: f_equal.
    by rewrite GRing.mulfVK //; solve_neq0.
  rewrite GRing.mulNr GRing.subrK => ev.
  have /eqP: 1 * (v ^+ 3) ^+2 + q * v ^+ 3 - p ^+ 3 / 27%:R = 0.
    apply: (@GRing.mulfI _ (v ^- 3)); solve_neq0.
    rewrite GRing.mulr0 -{}ev /v'; ssfield; solve_neq0.
  rewrite quadratic; last exact: GRing.oner_neq0.
  rewrite GRing.mulr1 GRing.mulrN GRing.opprK GRing.mulr1 2!inE => ev'.
  wlog ev: v @v' vn0 {ev ev'} /
           v ^+ 3 = (- q + sqrtC (q ^+ 2 + 4%:R * (p ^+ 3 / 27%:R))) / 2%:R.
    case/orP: ev' => [] /eqP ev'; first by eauto.
    move/(_ v'); rewrite (_ : - (p / (3%:R * v')) = v); last first.
      rewrite /v'; ssfield; solve_neq0.
    rewrite /= (GRing.addrC v' v); apply.
      by rewrite /v' GRing.oppr_eq0; solve_neq0; rewrite negb_or pn0.
    have ->: v' ^+ 3 = v ^+ 3 + v' ^+ 3 + q - v ^+ 3 - q by ssring.
    by rewrite ev ev'; ssfield; solve_neq0.
  have {ev} ev: v ^+ 3 = u ^+ 3.
    rewrite ev /u rootCK // GRing.mulrDl; congr GRing.add.
    rewrite {1}(_ : q ^+ 2 = 4%:R * (q ^+ 2 / 4%:R)); last first.
      by ssfield; solve_neq0.
    rewrite -GRing.mulrDr rootCMl; last by rewrite -[0]/0%:R leC_nat.
    rewrite -(@sqrCK 2%:R); last by rewrite -[0]/0%:R leC_nat.
    by rewrite -GRing.natrX -[2 ^ 2]/4; ssfield; rewrite sqrtC_eq0; solve_neq0.
  have un0 : u != 0.
    suff : u ^+ 3 != 0 by rewrite GRing.expf_eq0.
    by rewrite -ev GRing.expf_eq0.
  have {ev} /(prim_rootP prim_s) [i ev] : (v / u) ^+ 3 = 1.
    by rewrite GRing.expr_div_n -ev GRing.divff //; solve_neq0.
  by exists i; rewrite -ev -[3%:R * _ * _]GRing.mulrA GRing.mulfVK //.
case=> [i /eqP -> {x}].
have eu : u ^+ 6 + q * u ^+ 3 - p ^+ 3 / 27%:R = 0.
  rewrite -(GRing.mul1r (u ^+ 6)) -{1}[6]/(3 * 2)%N GRing.exprM.
  apply/eqP; rewrite quadratic ?GRing.oner_neq0 //.
  rewrite inE; apply/orP; left; apply/eqP.
  rewrite !GRing.mulr1 GRing.mulrN GRing.opprK {}/u.
  rewrite rootCK // GRing.mulrDl; congr GRing.add.
  rewrite {2}(_ : q ^+ 2 = 4%:R * (q ^+ 2 / 4%:R)); last first.
    by ssfield; solve_neq0.
  rewrite -GRing.mulrDr rootCMl; last by rewrite -[0]/0%:R leC_nat.
  rewrite -(@sqrCK 2%:R); last by rewrite -[0]/0%:R leC_nat.
  by rewrite -GRing.natrX -[2 ^ 2]/4; ssfield; rewrite sqrtC_eq0; solve_neq0.
have un0 : u != 0.
  move/eqP: eu; apply: contraTN => /eqP ->.
  rewrite !GRing.expr0n /= GRing.add0r GRing.mulr0 GRing.add0r.
  by solve_neq0; rewrite negb_or pn0.
rewrite -GRing.mulrA; set u1 := s ^+ i * u.
have s3 : s ^+ i ^+ 3 = 1.
  rewrite -GRing.exprM mulnC GRing.exprM (prim_expr_order prim_s).
  by rewrite GRing.expr1n.
have sin0 : s ^+ i != 0.
  by move: (GRing.oner_neq0 algCring); rewrite -s3 GRing.expf_eq0.
have u1n0 : u1 != 0 by rewrite /u1 GRing.mulf_eq0 negb_or sin0.
set u2 := - (p / (3%:R * u1)).
have ->: (u1 + u2) ^+ 3 = u1 ^+ 3 + u2 ^+ 3 + 3%:R * u1 * u2 * (u1 + u2).
  by move: (u1) (u2)=> u1' u2'; ssring.
have ->: 3%:R * u1 * u2 = - p.
  rewrite /u2 GRing.mulrC GRing.mulNr; apply: f_equal.
  by rewrite GRing.mulfVK //; solve_neq0.
rewrite GRing.mulNr GRing.subrK.
apply: (GRing.mulfI (_ : u1 ^+ 3 != 0)); first by rewrite /u1; solve_neq0.
rewrite GRing.mulr0 2!GRing.mulrDr -GRing.expr2.
rewrite -GRing.exprMn_comm; last exact: GRing.mulrC.
have -> : u1 * u2 = - (p / 3%:R).
  rewrite /u2; move: (u1) u1n0=> u1' u1n0'.
  ssfield; solve_neq0.
rewrite /u1 GRing.exprMn_comm; last exact: GRing.mulrC.
rewrite s3 GRing.mul1r -eu.
by ssfield; solve_neq0.
Qed.

End Cubic.
