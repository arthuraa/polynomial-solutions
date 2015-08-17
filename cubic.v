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

Require Import Field.

Lemma algC_ring_theory :
  @ring_theory algC 0 1 +%R *%R (fun x y => x - y) -%R eq.
Proof.
constructor=> //.
- exact: GRing.add0r.
- exact: GRing.addrC.
- exact: GRing.addrA.
- exact: GRing.mul1r.
- exact: GRing.mulrC.
- exact: GRing.mulrA.
- exact: GRing.mulrDl.
exact: GRing.subrr.
Qed.

Lemma algC_field_theory :
  @Field_theory.field_theory algC 0 1 +%R *%R (fun x y => x - y) -%R
                             (fun x y => x / y) (fun x => GRing.inv x) eq.
Proof.
split => //; first exact algC_ring_theory.
  apply/eqP/GRing.oner_neq0.
move=> p /eqP pn0; rewrite GRing.mulVf //.
Qed.

Add Field algC_field : algC_field_theory.

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
rewrite -[X in X == 0](@GRing.mulKf _ (3%:R ^+ 3 * a ^+ 2)); last first.
  rewrite GRing.mulf_eq0 2!GRing.expf_eq0 /= (negbTE an0) !orbF.
  by rewrite -[0]/(0%:R) eqC_nat.
rewrite ![(_ * _) * (_ + _)]GRing.mulrDr.
set k := _^-1.
rewrite -{4}(GRing.natrX _ 3 3) /expn /= /muln /=.
rewrite -GRing.mulrA (GRing.mulrA (a ^+ 2)) (GRing.mulrC (a ^+ 2)) -GRing.exprS.
rewrite -2!GRing.exprMn GRing.mulrA.
rewrite (GRing.exprS 3%:R) -[3%:R * _ * a ^+ 2]GRing.mulrA -GRing.exprMn.
rewrite -[3%:R * _ ^+ 2 * _]GRing.mulrA [(3%:R * a) ^+ 2 * (_ * _)]GRing.mulrA.
rewrite [_ * b]GRing.mulrC -[b * _ * _]GRing.mulrA -GRing.exprMn.
rewrite [_ * (b * _)]GRing.mulrA.
rewrite (GRing.expr2 (3%:R * a)).
rewrite GRing.mulrA -[_ * _ * (c * x)]GRing.mulrA.
rewrite [_ * (c * x)]GRing.mulrA [_ * c]GRing.mulrC -[c * _ * _]GRing.mulrA.
rewrite [3%:R * (3%:R * a)]GRing.mulrA -GRing.natrM /muln /=.
rewrite [9%:R * _ * _]GRing.mulrA.
rewrite -(GRing.addrK y x); set x' : algC := x + y.
rewrite GRing.mulrBr [_ * y]GRing.mulrC [in LHS]/y GRing.mulfVK; last first.
  by rewrite GRing.mulf_eq0 -[0]/0%:R eqC_nat.
set x'' := 3%:R * a * x'.
rewrite 2!GRing.exprBn GRing.mulrBr.
rewrite !big_ord_recr /= !big_ord0 GRing.add0r GRing.expr0 GRing.mul1r.
rewrite /subn /= /binomial /= /addn /= !GRing.expr0 !GRing.expr1 !GRing.mulN1r.
rewrite GRing.add0r GRing.mul1r !GRing.mulr1 GRing.mulr1n.
do ![rewrite -GRing.signr_odd /= (GRing.expr0, GRing.expr1)].
rewrite !GRing.mulNr !GRing.mulNrn.
rewrite GRing.mul1r (GRing.mulrDr (3%:R * b)) !GRing.addrA !GRing.mulr1n.
rewrite !GRing.mul1r -[_ * b * b ^+ 2]GRing.mulrA -GRing.exprS.
rewrite -(GRing.addrA _ _ (x'' * b ^+ 2)) -GRing.mulr2n -(GRing.addrA _ (x'' * b ^+ 2)).
rewrite -GRing.mulrS GRing.mulrBr.
rewrite -[_ - b ^+ 3 + _]GRing.addrA [- b ^+ 3 + _]GRing.addrC [_ + (_ - b ^+ 3)]GRing.addrA.
rewrite -[_ - b ^+ 3 + _]GRing.addrA [- b ^+ 3 + _]GRing.addrC.
rewrite [_ * b ^+ 3]GRing.mulr_natl (GRing.mulrSr (b ^+ 3)) GRing.addrK.
rewrite -[b ^+ 3 *+ 2]GRing.mulr_natl.
rewrite -[_ + _ * b ^+ 3 + _]GRing.addrA [_ * b ^+ 3 + _]GRing.addrC.
rewrite [_ + (_ + _ * b ^+ 3)]GRing.addrA [_ + (_ - _)]GRing.addrA.
rewrite -[_ - x'' ^+ 2 * b *+ 3 + _]GRing.addrA [x'' ^+ 2 * _ *- _ + _]GRing.addrC.
rewrite GRing.addrA -[(_ * b) *+ 3]GRing.mulr_natl.
rewrite -[3%:R * b * _]GRing.mulrA [b * _ ^+ _]GRing.mulrC GRing.subrK.
rewrite [x'' * _]GRing.mulrC -GRing.mulr_natr [_ * 3%:R]GRing.mulrC.
rewrite -(GRing.mulr_natr _ 2) (GRing.mulrC x'' b) 2!(GRing.mulrA (3%:R * b)).
rewrite -[_ * b * b]GRing.mulrA -GRing.expr2 (GRing.mulrA 3%:R).
rewrite (GRing.mulrC _ 2%:R) 2!(GRing.mulrA 2%:R) -GRing.natrM.
rewrite /muln /=.
rewrite -(GRing.mulrA 3%:R) -(GRing.mulrA 6%:R) -(GRing.addrA (x'' ^+ 3)).
rewrite -GRing.mulrBl -(GRing.opprK (3%:R - 6%:R)) GRing.opprB -GRing.natrB //.
rewrite /subn /= -[in LHS]GRing.mulr_natr GRing.mulNr GRing.mul1r.
rewrite (GRing.mulrA 3%:R) -(GRing.addrA (x'' ^+ 3)) [- _ + _]GRing.addrC.
rewrite -GRing.mulrBl -GRing.addrA -(GRing.addrA _ (2%:R * b ^+ 3)).
rewrite (GRing.addrA (2%:R * b ^+ 3)).
rewrite -(GRing.mulrA _ c b) (GRing.mulrC c b) (GRing.mulrA _ b c).
rewrite (_ : k = a * (3%:R * a)^-3); last first.
  rewrite /k; apply/(canRL (GRing.mulVKf an0)).
  rewrite GRing.mulrC -GRing.invfM.
  rewrite -GRing.mulrA -GRing.exprSr -GRing.exprMn_comm //.
  exact: GRing.mulrC.
rewrite {}/k -(GRing.mulrA a) GRing.mulf_eq0 (negbTE an0) /=.
rewrite 2!(GRing.mulrDr) [X in _ + _ + X]GRing.mulrC.
rewrite {1}/x'' [(_ * x') ^+ 3]GRing.exprMn_comm; last exact: GRing.mulrC.
rewrite GRing.mulKf; last first.
  rewrite GRing.expf_eq0 /= GRing.mulf_eq0 (negbTE an0) orbF.
  by rewrite -[0]/0%:R eqC_nat.
rewrite {2}GRing.exprMn_comm; last exact: GRing.mulrC.
rewrite -GRing.natrX /expn /= /muln /= -[X in _ + _ + X]/q.
rewrite [_ ^- 3 * _]GRing.mulrC -(GRing.mulrA _ x'').
rewrite [in x'' / _]GRing.exprS GRing.invfM (GRing.mulrA x'') /x''.
rewrite (GRing.mulrC _ x') GRing.mulfK; last first.
  by rewrite GRing.mulf_eq0 (negbTE an0) -[0]/0%:R eqC_nat.
rewrite [x' / _]GRing.mulrC GRing.mulrA.
rewrite GRing.exprMn_comm; last exact: GRing.mulrC.
rewrite (GRing.expr2 3%:R) -[9]/(3 * 3)%N.
rewrite GRing.natrM -2!(GRing.mulrA 3%:R) -GRing.mulrBr [3%:R * _]GRing.mulrC.
rewrite -[3%:R * 3%:R * _]GRing.mulrA GRing.invfM GRing.mulrA.
rewrite GRing.mulfK; last by rewrite -[0]/0%:R eqC_nat.
rewrite -[X in _ + X * _ + _]/p {}/x''.
transitivity [exists i : 'I_3,
                x' == (if p == 0 then s ^+ i * 3.-root (- q)
                       else s ^+ i * u - p / (3%:R * s ^+ i * u))]; last first.
  apply: eq_existsb=> i.
  rewrite [in RHS]fun_if [_ - y]GRing.addrC !(inj_eq (GRing.addrI _)).
  by rewrite -fun_if.
move: x' p q @u => {x y a b c d an0} x p q u.
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
admit.
Qed.