import PEqualNP.Defs
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace PEqualNP.Outside.L_lib_1280_aux

open PEqualNP.CircuitLowerBounds

def GateOK (m : ℕ) (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) ∧
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < m + j

def isNotOp : GateOp → Bool
  | GateOp.not => true
  | _ => false

def notCnt (gs : List Gate) : ℕ :=
  (gs.filter fun g => isNotOp g.op).length

def evalWires (gs : List Gate) (inp : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) inp

def wVal (gs : List Gate) (inp : List Bool) (i : ℕ) : Bool :=
  (evalWires gs inp).getD i false

lemma evalWires_length (gs : List Gate) (inp : List Bool) :
    (evalWires gs inp).length = inp.length + gs.length := by
  induction gs generalizing inp with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    rw [ih]
    simp; omega

lemma evalWires_append (g1 g2 : List Gate) (inp : List Bool) :
    evalWires (g1 ++ g2) inp = evalWires g2 (evalWires g1 inp) := by
  simp [evalWires, List.foldl_append]

lemma evalWires_prefix_getD (g1 g2 : List Gate) (inp : List Bool) {i : ℕ}
    (hi : i < inp.length + g1.length) :
    wVal (g1 ++ g2) inp i = wVal g1 inp i := by
  unfold wVal
  rw [evalWires_append]
  have hiw : i < (evalWires g1 inp).length := by rw [evalWires_length]; exact hi
  generalize evalWires g1 inp = w at hiw ⊢
  induction g2 generalizing w with
  | nil => simp [evalWires]
  | cons g gs ih =>
    simp only [evalWires, List.foldl_cons] at ih ⊢
    have hi' : i < (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]).length := by
      simp; omega
    rw [ih (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]) hi']
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hiw]

lemma evalWires_input (gs : List Gate) (inp : List Bool) {i : ℕ} (hi : i < inp.length) :
    wVal gs inp i = inp.getD i false := by
  have h := evalWires_prefix_getD [] gs inp (i := i) (by simpa using hi)
  simpa [wVal, evalWires] using h

lemma notCnt_append (g1 g2 : List Gate) : notCnt (g1 ++ g2) = notCnt g1 + notCnt g2 := by
  simp [notCnt, List.filter_append]

lemma GateOK_nil (m : ℕ) : GateOK m [] := by
  refine ⟨by simp, fun j hj => by simp at hj⟩

lemma GateOK_append_gate {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2)
    (hin : ∀ i ∈ g.inputs, i < m + gs.length) :
    GateOK m (gs ++ [g]) := by
  refine ⟨?_, ?_⟩
  · intro g' hg'
    simp only [List.mem_append, List.mem_singleton] at hg'
    rcases hg' with hg' | rfl
    · exact hgs.1 g' hg'
    · exact ⟨hop, hlen⟩
  · intro j hj i hi
    simp only [List.length_append, List.length_singleton] at hj
    by_cases hlt : j < gs.length
    · have hget : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
      rw [hget] at hi
      exact hgs.2 j hlt i hi
    · have hjeq : j = gs.length := by omega
      subst hjeq
      have hget : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at hi
      exact hin i hi

lemma wVal_append_gate (gs : List Gate) (g : Gate) (inp : List Bool) :
    wVal (gs ++ [g]) inp (inp.length + gs.length) =
    g.op.eval (g.inputs.map fun i => wVal gs inp i) := by
  unfold wVal
  rw [evalWires_append]
  have hlen : (evalWires gs inp).length = inp.length + gs.length := evalWires_length gs inp
  generalize evalWires gs inp = w at hlen ⊢
  simp only [evalWires, List.foldl_cons, List.foldl_nil, List.getD_eq_getElem?_getD, ← hlen]
  rw [List.getElem?_append_right le_rfl]
  simp

lemma mkAnd_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.and, [a, b]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = (wVal gs inp a && wVal gs inp b)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.and, [a, b]⟩ (Or.inl rfl) (by simp)
      (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

lemma mkOr_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.or, [a, b]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = (wVal gs inp a || wVal gs inp b)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.or, [a, b]⟩ (Or.inr (Or.inl rfl)) (by simp)
      (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

lemma mkNot_step {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a : ℕ}
    (ha : a < m + gs.length) :
    let gs' := gs ++ [⟨GateOp.not, [a]⟩]
    let w := m + gs.length
    GateOK m gs' ∧ notCnt gs' = notCnt gs + 1 ∧ gs'.length = gs.length + 1 ∧
    w < m + gs'.length ∧
    (∀ inp : List Bool, inp.length = m →
      (∀ i < m + gs.length, wVal gs' inp i = wVal gs inp i) ∧
      wVal gs' inp w = !(wVal gs inp a)) := by
  dsimp only
  refine ⟨GateOK_append_gate hgs ⟨GateOp.not, [a]⟩ (Or.inr (Or.inr rfl)) (by simp)
      (by intro i hi; simp at hi; subst hi; exact ha),
    by simp [notCnt, isNotOp, List.filter_append], by simp, by simp, ?_⟩
  intro inp hinp
  constructor
  · intro i hi; exact evalWires_prefix_getD gs _ inp (by omega)
  · rw [← hinp, wVal_append_gate]
    simp [GateOp.eval]

def Extends (gs gs' : List Gate) : Prop := ∃ suf, gs' = gs ++ suf

lemma Extends.refl (gs : List Gate) : Extends gs gs := ⟨[], by simp⟩

lemma Extends.trans {g1 g2 g3 : List Gate} (h1 : Extends g1 g2) (h2 : Extends g2 g3) :
    Extends g1 g3 := by
  rcases h1 with ⟨s1, rfl⟩; rcases h2 with ⟨s2, rfl⟩
  exact ⟨s1 ++ s2, by simp [List.append_assoc]⟩

lemma Extends.length_le {g1 g2 : List Gate} (h : Extends g1 g2) : g1.length ≤ g2.length := by
  rcases h with ⟨s, rfl⟩; simp

lemma Extends.wVal_eq {g1 g2 : List Gate} (h : Extends g1 g2) (inp : List Bool)
    {i : ℕ} (hi : i < inp.length + g1.length) :
    wVal g2 inp i = wVal g1 inp i := by
  rcases h with ⟨s, rfl⟩
  exact evalWires_prefix_getD g1 s inp hi

lemma Extends.map_wVal_eq {g1 g2 : List Gate} (h : Extends g1 g2) (inp : List Bool)
    (ws : List ℕ) (hws : ∀ w ∈ ws, w < inp.length + g1.length) :
    ws.map (wVal g2 inp) = ws.map (wVal g1 inp) := by
  apply List.map_congr_left
  intro w hw
  exact h.wVal_eq inp (hws w hw)

lemma mkAnd_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = (wVal gs inp a && wVal gs inp b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkAnd_step hgs ha hb
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

lemma mkOr_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a b : ℕ}
    (ha : a < m + gs.length) (hb : b < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = (wVal gs inp a || wVal gs inp b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkOr_step hgs ha hb
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

lemma mkNot_ex {m : ℕ} {gs : List Gate} (hgs : GateOK m gs) {a : ℕ}
    (ha : a < m + gs.length) :
    ∃ (gs' : List Gate) (w : ℕ),
      Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs + 1 ∧ gs'.length = gs.length + 1 ∧
      w < m + gs'.length ∧
      ∀ inp : List Bool, inp.length = m →
        wVal gs' inp w = !(wVal gs inp a) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := mkNot_step hgs ha
  exact ⟨_, _, ⟨_, rfl⟩, h1, h2, h3, h4, fun inp hinp => (h5 inp hinp).2⟩

def IsSortedDesc (L : List Bool) : Prop :=
  L = List.replicate (L.count true) true ++ List.replicate (L.length - L.count true) false

def IsBitonic (L : List Bool) : Prop :=
  ∃ (a b : ℕ), a ≤ b ∧ b ≤ L.length ∧
    (L = List.replicate a true ++ List.replicate (b - a) false ++ List.replicate (L.length - b) true ∨
     L = List.replicate a false ++ List.replicate (b - a) true ++ List.replicate (L.length - b) false)

lemma count_true_le_length (L : List Bool) : L.count true ≤ L.length :=
  List.count_le_length

lemma getElem_isSortedDesc {L : List Bool} (hS : IsSortedDesc L) {i : ℕ} (hi : i < L.length) :
    L[i] = decide (i < L.count true) := by
  have hlen : L.count true ≤ L.length := count_true_le_length L
  have hget : L[i]? = some (decide (i < L.count true)) := by
    conv_lhs => rw [hS]
    by_cases hic : i < L.count true
    · rw [List.getElem?_append_left (by simp [hic])]
      simp [hic]
    · rw [List.getElem?_append_right (by simp; omega)]
      simp only [List.length_replicate]
      rw [List.getElem?_replicate]
      simp [hic, (by omega : i - L.count true < L.length - L.count true)]
  have := List.getElem?_eq_getElem hi
  rw [this] at hget
  exact Option.some.inj hget

lemma isSortedDesc_iff_getElem (L : List Bool) :
    IsSortedDesc L ↔ ∀ (i : ℕ) (hi : i < L.length), L[i] = decide (i < L.count true) := by
  constructor
  · intro hS i hi; exact getElem_isSortedDesc hS hi
  · intro h
    unfold IsSortedDesc
    have hlen : L.count true ≤ L.length := count_true_le_length L
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      rw [h i hi1]
      by_cases hic : i < L.count true
      · rw [List.getElem_append_left (by simp [hic])]
        simp [hic]
      · rw [List.getElem_append_right (by simp; omega)]
        simp [hic]

lemma isSortedDesc_of_all_false {L : List Bool} (h : ∀ b ∈ L, b = false) : IsSortedDesc L := by
  have hc : L.count true = 0 := by
    rw [List.count_eq_zero]
    intro hmem; exact Bool.noConfusion (h true hmem)
  rw [isSortedDesc_iff_getElem]
  intro i hi
  rw [hc]; simp [h L[i] (List.getElem_mem hi)]

lemma isSortedDesc_of_all_true {L : List Bool} (h : ∀ b ∈ L, b = true) : IsSortedDesc L := by
  have hc : L.count true = L.length := by
    induction L with
    | nil => simp
    | cons x xs ih =>
      have hx : x = true := h x (by simp)
      subst hx
      simp [ih (fun b hb => h b (by simp [hb]))]
  rw [isSortedDesc_iff_getElem]
  intro i hi
  rw [hc]; simp [hi, h L[i] (List.getElem_mem hi)]

lemma isBitonic_of_sorted_append_rev {L1 L2 : List Bool} (h1 : IsSortedDesc L1) (h2 : IsSortedDesc L2) :
    IsBitonic (L1 ++ L2.reverse) := by
  let c1 := L1.count true
  let c2 := L2.count true
  have hc1 : c1 ≤ L1.length := count_true_le_length L1
  have hc2 : c2 ≤ L2.length := count_true_le_length L2
  refine ⟨c1, L1.length + (L2.length - c2), by omega, by simp, Or.inl ?_⟩
  conv_lhs => rw [h1, h2]
  rw [List.reverse_append, List.reverse_replicate, List.reverse_replicate]
  simp only [List.length_append, List.length_reverse]
  have h1' : L1.length + (L2.length - c2) - c1 = (L1.length - c1) + (L2.length - c2) := by omega
  have h2' : L1.length + L2.length - (L1.length + (L2.length - c2)) = c2 := by omega
  rw [h1', h2']
  dsimp only [c1, c2]
  rw [List.replicate_add]
  simp only [List.append_assoc]

lemma isBitonic_map_not {L : List Bool} (h : IsBitonic L) : IsBitonic (L.map (!·)) := by
  rcases h with ⟨a, b, hab, hbl, hL | hL⟩
  · refine ⟨a, b, hab, by simp [hbl], Or.inr ?_⟩
    conv_lhs => rw [hL]
    simp [List.map_append, List.map_replicate]
  · refine ⟨a, b, hab, by simp [hbl], Or.inl ?_⟩
    conv_lhs => rw [hL]
    simp [List.map_append, List.map_replicate]

lemma count_true_ofFn_eq (n : ℕ) (f : Fin n → Bool) :
    (List.ofFn f).count true = ∑ i : Fin n, if f i then 1 else 0 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
    cases f 0 <;> simp [Nat.add_comm]

lemma count_true_ofFn_or_and (h : ℕ) (L : List Bool) (hL : L.length = 2 * h) :
    (List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false)).count true +
    (List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false)).count true =
    L.count true := by
  rw [count_true_ofFn_eq, count_true_ofFn_eq, ← Finset.sum_add_distrib]
  have hsum : ∑ i : Fin h,
      ((if (L.getD i.1 false || L.getD (i.1 + h) false) then 1 else 0) +
       (if (L.getD i.1 false && L.getD (i.1 + h) false) then 1 else 0)) =
      ∑ i : Fin h, ((if L.getD i.1 false then 1 else 0) + (if L.getD (i.1 + h) false then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro i _
    cases L.getD i.1 false <;> cases L.getD (i.1 + h) false <;> rfl
  rw [hsum, Finset.sum_add_distrib]
  have htake : (L.take h).count true = ∑ i : Fin h, if L.getD i.1 false then 1 else 0 := by
    have hEq : L.take h = List.ofFn (fun i : Fin h => L.getD i.1 false) := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2
        have hih : i < h := by simp at hi2; exact hi2
        simp only [List.getElem_take, List.getElem_ofFn, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by omega)]; rfl
    rw [hEq, count_true_ofFn_eq]
  have hdrop : (L.drop h).count true = ∑ i : Fin h, if L.getD (i.1 + h) false then 1 else 0 := by
    have hEq : L.drop h = List.ofFn (fun i : Fin h => L.getD (i.1 + h) false) := by
      apply List.ext_getElem
      · simp; omega
      · intro i hi1 hi2
        have hih : i < h := by simp at hi2; exact hi2
        simp only [List.getElem_drop, List.getElem_ofFn, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by omega)]
        simp [Nat.add_comm]
    rw [hEq, count_true_ofFn_eq]
  rw [← htake, ← hdrop, ← List.count_append, List.take_append_drop]

lemma bitonic_layer_type1 {h a b : ℕ} (hab : a ≤ b) (hbl : b ≤ 2 * h) :
    let L := List.replicate a true ++ List.replicate (b - a) false ++ List.replicate (2 * h - b) true
    let hi := List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false)
    let lo := List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false)
    IsBitonic hi ∧ IsBitonic lo ∧
    ((∀ x ∈ lo, x = false) ∨ (∀ x ∈ hi, x = true)) := by
  intro L hi lo
  have hLlen : L.length = 2 * h := by simp [L]; omega
  have hLget : ∀ idx < 2 * h, L.getD idx false = decide (idx < a ∨ b ≤ idx) := by
    intro idx hidx
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : idx < L.length)]
    dsimp only [Option.getD_some, L]
    by_cases h1 : idx < a
    · rw [List.getElem_append_left (by simp; omega)]
      rw [List.getElem_append_left (by simp; omega)]
      simp [h1]
    · by_cases h2 : idx < b
      · rw [List.getElem_append_left (by simp; omega)]
        rw [List.getElem_append_right (by simp; omega)]
        simp [h1, h2]
      · rw [List.getElem_append_right (by simp; omega)]
        simp [h1, (by omega : b ≤ idx)]
  have hget_ext : ∀ (M : List Bool) (a' b' : ℕ), a' ≤ b' → b' ≤ h → M.length = h →
      (∀ i < h, M.getD i false = decide (i < a' ∨ b' ≤ i)) →
      M = List.replicate a' true ++ List.replicate (b' - a') false ++ List.replicate (h - b') true := by
    intro M a' b' ha' hb' hMl hMg
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      have := hMg i (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1] at this
      dsimp only [Option.getD_some] at this
      rw [this]
      by_cases h1 : i < a'
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
        simp [h1]
      · by_cases h2 : i < b'
        · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
          simp [h1, h2]
        · rw [List.getElem_append_right (by simp; omega)]
          simp [h1, (by omega : b' ≤ i)]
  have hget_ext2 : ∀ (M : List Bool) (a' b' : ℕ), a' ≤ b' → b' ≤ h → M.length = h →
      (∀ i < h, M.getD i false = decide (a' ≤ i ∧ i < b')) →
      M = List.replicate a' false ++ List.replicate (b' - a') true ++ List.replicate (h - b') false := by
    intro M a' b' ha' hb' hMl hMg
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      have := hMg i (by omega)
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi1] at this
      dsimp only [Option.getD_some] at this
      rw [this]
      by_cases h1 : i < a'
      · rw [List.getElem_append_left (by simp; omega), List.getElem_append_left (by simp; omega)]
        simp [h1]
      · by_cases h2 : i < b'
        · rw [List.getElem_append_left (by simp; omega), List.getElem_append_right (by simp; omega)]
          simp [(by omega : a' ≤ i), h2]
        · rw [List.getElem_append_right (by simp; omega)]
          simp [h2]
  by_cases hba : h ≤ b - a
  ·
    have hloF : ∀ x ∈ lo, x = false := by
      intro x hx
      simp only [lo, List.mem_ofFn] at hx
      rcases hx with ⟨i, rfl⟩
      rw [hLget i.1 (by omega), hLget (i.1 + h) (by omega)]
      have hnot : ¬ ((i.1 < a ∨ b ≤ i.1) ∧ (i.1 + h < a ∨ b ≤ i.1 + h)) := by omega
      cases h1 : decide (i.1 < a ∨ b ≤ i.1) <;> cases h2 : decide (i.1 + h < a ∨ b ≤ i.1 + h)
      · rfl
      · rfl
      · rfl
      · exfalso
        exact hnot ⟨of_decide_eq_true h1, of_decide_eq_true h2⟩
    have hlo_eq : lo = List.replicate 0 true ++ List.replicate (h - 0) false ++ List.replicate (h - h) true := by
      apply hget_ext lo 0 h (by omega) le_rfl (by simp [lo])
      intro i hi'
      have hmem : lo.getD i false = false := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [lo]; omega)]
        exact hloF _ (List.getElem_mem _)
      rw [hmem]; simp; omega
    have hhi_eq : hi = List.replicate a true ++ List.replicate ((b - h) - a) false ++ List.replicate (h - (b - h)) true := by
      apply hget_ext hi a (b - h) (by omega) (by omega) (by simp [hi])
      intro i hi'
      have hgi : hi.getD i false = (L.getD i false || L.getD (i + h) false) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]; omega)]
        simp [hi]
      rw [hgi, hLget i (by omega), hLget (i + h) (by omega)]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      omega
    exact ⟨⟨a, b - h, by omega, by simp [hi]; omega, Or.inl (by simpa [hi] using hhi_eq)⟩,
      ⟨0, h, by omega, by simp [lo], Or.inl (by simpa [lo] using hlo_eq)⟩,
      Or.inl hloF⟩
  ·
    have hhiT : ∀ x ∈ hi, x = true := by
      intro x hx
      simp only [hi, List.mem_ofFn] at hx
      rcases hx with ⟨i, rfl⟩
      rw [hLget i.1 (by omega), hLget (i.1 + h) (by omega)]
      rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      omega
    have hhi_eq : hi = List.replicate h true ++ List.replicate (h - h) false ++ List.replicate (h - h) true := by
      apply hget_ext hi h h le_rfl le_rfl (by simp [hi])
      intro i hi'
      have hmem : hi.getD i false = true := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]; omega)]
        exact hhiT _ (List.getElem_mem _)
      rw [hmem]; simp [hi']
    have hlo_bit : IsBitonic lo := by
      by_cases hbh : b ≤ h
      · refine ⟨a, b, hab, by simp [lo]; omega, Or.inl ?_⟩
        simpa [lo] using hget_ext lo a b hab hbh (by simp [lo]) (fun i hi' => by
          have hgi : lo.getD i false = (L.getD i false && L.getD (i + h) false) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [lo]; omega)]; simp [lo]
          rw [hgi, hLget i (by omega), hLget (i + h) (by omega)]
          apply Bool.eq_iff_iff.2
          simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
      · by_cases hah : h ≤ a
        · refine ⟨a - h, b - h, by omega, by simp [lo]; omega, Or.inl ?_⟩
          simpa [lo] using hget_ext lo (a - h) (b - h) (by omega) (by omega) (by simp [lo]) (fun i hi' => by
            have hgi : lo.getD i false = (L.getD i false && L.getD (i + h) false) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [lo]; omega)]; simp [lo]
            rw [hgi, hLget i (by omega), hLget (i + h) (by omega)]
            apply Bool.eq_iff_iff.2
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
        · refine ⟨b - h, a, by omega, by simp [lo]; omega, Or.inr ?_⟩
          simpa [lo] using hget_ext2 lo (b - h) a (by omega) (by omega) (by simp [lo]) (fun i hi' => by
            have hgi : lo.getD i false = (L.getD i false && L.getD (i + h) false) := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [lo]; omega)]; simp [lo]
            rw [hgi, hLget i (by omega), hLget (i + h) (by omega)]
            apply Bool.eq_iff_iff.2
            simp only [Bool.and_eq_true, decide_eq_true_eq]; omega)
    exact ⟨⟨h, h, le_rfl, by simp [hi], Or.inl (by simpa [hi] using hhi_eq)⟩, hlo_bit, Or.inr hhiT⟩

lemma bitonic_layer {h : ℕ} {L : List Bool} (hL : L.length = 2 * h) (hB : IsBitonic L) :
    let hi := List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false)
    let lo := List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false)
    IsBitonic hi ∧ IsBitonic lo ∧
    ((∀ x ∈ lo, x = false) ∨ (∀ x ∈ hi, x = true)) := by
  rcases hB with ⟨a, b, hab, hbl, hEq | hEq⟩
  · rw [hL] at hbl hEq
    subst hEq
    exact bitonic_layer_type1 hab hbl
  · rw [hL] at hbl hEq
    let L' := List.replicate a true ++ List.replicate (b - a) false ++ List.replicate (2 * h - b) true
    have hLmap : L = L'.map (!·) := by
      rw [hEq]; simp [L', List.map_append, List.map_replicate]
    have h1 := bitonic_layer_type1 hab hbl
    dsimp only at h1 ⊢
    have hL'len : L'.length = 2 * h := by simp [L']; omega
    have hget : ∀ idx < 2 * h, L.getD idx false = !(L'.getD idx false) := by
      intro idx hidx
      rw [hLmap]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp [hL'len]; omega),
          List.getElem?_eq_getElem (by omega : idx < L'.length)]
      simp
    have hhi_eq : List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false) =
        (List.ofFn (fun i : Fin h => L'.getD i.1 false && L'.getD (i.1 + h) false)).map (!·) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        have hih : i < h := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn, List.getElem_map]
        rw [hget i (by omega), hget (i + h) (by omega)]
        cases L'.getD i false <;> cases L'.getD (i + h) false <;> rfl
    have hlo_eq : List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false) =
        (List.ofFn (fun i : Fin h => L'.getD i.1 false || L'.getD (i.1 + h) false)).map (!·) := by
      apply List.ext_getElem
      · simp
      · intro i hi1 hi2
        have hih : i < h := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn, List.getElem_map]
        rw [hget i (by omega), hget (i + h) (by omega)]
        cases L'.getD i false <;> cases L'.getD (i + h) false <;> rfl
    rw [hhi_eq, hlo_eq]
    refine ⟨isBitonic_map_not h1.2.1, isBitonic_map_not h1.1, ?_⟩
    rcases h1.2.2 with hloF | hhiT
    · right; intro x hx
      simp only [List.mem_map] at hx; rcases hx with ⟨y, hy, rfl⟩
      rw [hloF y hy]; rfl
    · left; intro x hx
      simp only [List.mem_map] at hx; rcases hx with ⟨y, hy, rfl⟩
      rw [hhiT y hy]; rfl

lemma isSortedDesc_append_of_const {L1 L2 : List Bool}
    (h1 : IsSortedDesc L1) (h2 : IsSortedDesc L2)
    (hconst : (∀ x ∈ L2, x = false) ∨ (∀ x ∈ L1, x = true)) :
    IsSortedDesc (L1 ++ L2) := by
  have hc1 := count_true_le_length L1
  have hc2 := count_true_le_length L2
  rcases hconst with hF | hT
  · have hc20 : L2.count true = 0 := by
      rw [List.count_eq_zero]; intro hm; exact Bool.noConfusion (hF true hm)
    unfold IsSortedDesc at h1 h2 ⊢
    rw [List.count_append, hc20, add_zero, List.length_append]
    conv_lhs => rw [h1, h2]
    rw [hc20]; simp only [List.replicate_zero, List.nil_append, Nat.sub_zero, List.append_assoc]
    rw [← List.replicate_add]
    congr 2; omega
  · have hc1l : L1.count true = L1.length := by
      have hall : ∀ (M : List Bool), (∀ x ∈ M, x = true) → M.count true = M.length := by
        intro M hM
        induction M with
        | nil => simp
        | cons x xs ih =>
          have hx : x = true := hM x (by simp); subst hx
          simp [ih (fun b hb => hM b (by simp [hb]))]
      exact hall L1 hT
    unfold IsSortedDesc at h1 h2 ⊢
    rw [List.count_append, hc1l, List.length_append]
    conv_lhs => rw [h1, h2]
    rw [hc1l]; simp only [Nat.sub_self, List.replicate_zero, List.append_nil, ← List.append_assoc]
    rw [← List.replicate_add]
    have hsub : L1.length + L2.length - (L1.length + L2.count true) = L2.length - L2.count true := by omega
    rw [hsub]

lemma rev_comp_eq (a b : Bool) :
    ((!(a || b)) || (b && !(a && b))) = !a ∧
    ((!(a || b)) || (a && !(a && b))) = !b := by
  cases a <;> cases b <;> decide

lemma exists_comp_layer {m : ℕ} : ∀ (h : ℕ) (gs : List Gate) (as bs : List ℕ),
    GateOK m gs → as.length = h → bs.length = h →
    (∀ w ∈ as, w < m + gs.length) → (∀ w ∈ bs, w < m + gs.length) →
    ∃ (gs1 : List Gate) (hi lo : List ℕ),
      Extends gs gs1 ∧ GateOK m gs1 ∧ notCnt gs1 = notCnt gs ∧
      gs1.length ≤ gs.length + 2 * h ∧
      hi.length = h ∧ lo.length = h ∧
      (∀ w ∈ hi, w < m + gs1.length) ∧ (∀ w ∈ lo, w < m + gs1.length) ∧
      (∀ inp : List Bool, inp.length = m →
        hi.map (wVal gs1 inp) = List.ofFn (fun i : Fin h => wVal gs inp (as.getD i.1 0) || wVal gs inp (bs.getD i.1 0)) ∧
        lo.map (wVal gs1 inp) = List.ofFn (fun i : Fin h => wVal gs inp (as.getD i.1 0) && wVal gs inp (bs.getD i.1 0))) ∧
      (∀ (gs2 : List Gate) (cHi cLo : List ℕ),
        Extends gs1 gs2 → GateOK m gs2 → cHi.length = h → cLo.length = h →
        (∀ w ∈ cHi, w < m + gs2.length) → (∀ w ∈ cLo, w < m + gs2.length) →
        ∃ (gs3 : List Gate) (rA rB : List ℕ),
          Extends gs2 gs3 ∧ GateOK m gs3 ∧ notCnt gs3 = notCnt gs2 ∧
          gs3.length ≤ gs2.length + 4 * h ∧
          rA.length = h ∧ rB.length = h ∧
          (∀ w ∈ rA, w < m + gs3.length) ∧ (∀ w ∈ rB, w < m + gs3.length) ∧
          ∀ inp : List Bool, inp.length = m →
            cHi.map (wVal gs2 inp) = (hi.map (wVal gs1 inp)).map (!·) →
            cLo.map (wVal gs2 inp) = (lo.map (wVal gs1 inp)).map (!·) →
            rA.map (wVal gs3 inp) = (as.map (wVal gs inp)).map (!·) ∧
            rB.map (wVal gs3 inp) = (bs.map (wVal gs inp)).map (!·)) := by
  intro h
  induction h with
  | zero =>
    intro gs as bs hgs has hbs _ _
    cases as; swap; simp at has
    cases bs; swap; simp at hbs
    refine ⟨gs, [], [], Extends.refl gs, hgs, rfl, by omega, rfl, rfl,
      by simp, by simp, fun _ _ => by simp, ?_⟩
    intro gs2 cHi cLo _ hgs2 hcH hcL _ _
    cases cHi; swap; simp at hcH
    cases cLo; swap; simp at hcL
    exact ⟨gs2, [], [], Extends.refl gs2, hgs2, rfl, by omega, rfl, rfl,
      by simp, by simp, fun _ _ _ _ => by simp⟩
  | succ k ih =>
    intro gs as bs hgs has hbs hasW hbsW
    cases as with
    | nil => simp at has
    | cons a as' =>
      cases bs with
      | nil => simp at hbs
      | cons b bs' =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at has hbs
        have ha : a < m + gs.length := hasW a (by simp)
        have hb : b < m + gs.length := hbsW b (by simp)
        obtain ⟨hgsA, hncA, hlenA, hu_lt, hevalA⟩ := mkOr_step hgs ha hb
        let gsA := gs ++ [⟨GateOp.or, [a, b]⟩]
        let u := m + gs.length
        have ha' : a < m + gsA.length := by simp [gsA]; omega
        have hb' : b < m + gsA.length := by simp [gsA]; omega
        obtain ⟨hgsB, hncB, hlenB, hv_lt, hevalB⟩ := mkAnd_step hgsA ha' hb'
        let gsB := gsA ++ [⟨GateOp.and, [a, b]⟩]
        let v := m + gsA.length
        have hext0B : Extends gs gsB := Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩
        have hlen0B : gsB.length = gs.length + 2 := by simp [gsB, gsA]
        obtain ⟨gs1, hi', lo', hextB1, hgs1, hnc1, hlen1, hhi'l, hlo'l, hhi'W, hlo'W, heval1, hrev1⟩ :=
          ih gsB as' bs' hgsB has hbs
            (fun w hw => by have := hasW w (by simp [hw]); omega)
            (fun w hw => by have := hbsW w (by simp [hw]); omega)
        have hext01 : Extends gs gs1 := hext0B.trans hextB1
        have hlenB' : gsB.length = gsA.length + 1 := hlenB
        have hlenA' : gsA.length = gs.length + 1 := hlenA
        have hu_lt1 : u < m + gs1.length := by have := hextB1.length_le; dsimp only [u]; omega
        have hv_lt1 : v < m + gs1.length := by have := hextB1.length_le; dsimp only [v]; omega
        have hnc01 : notCnt gs1 = notCnt gs := by rw [hnc1]; exact hncB.trans hncA
        refine ⟨gs1, u :: hi', v :: lo', hext01, hgs1, hnc01, by omega,
          by simp [hhi'l], by simp [hlo'l],
          fun w hw => by simp at hw; rcases hw with rfl | hw; exact hu_lt1; exact hhi'W w hw,
          fun w hw => by simp at hw; rcases hw with rfl | hw; exact hv_lt1; exact hlo'W w hw,
          ?_, ?_⟩
        · intro inp hinp
          have h1 := heval1 inp hinp
          have hA := hevalA inp hinp
          have hB := hevalB inp hinp
          have hu_val : wVal gs1 inp u = (wVal gs inp a || wVal gs inp b) := by
            have h1' : wVal gs1 inp u = wVal gsB inp u := hextB1.wVal_eq inp (by dsimp only [u]; omega)
            have h2' : wVal gsB inp u = wVal gsA inp u := hB.1 u (by dsimp only [u]; omega)
            rw [h1', h2', hA.2]
          have hv_val : wVal gs1 inp v = (wVal gs inp a && wVal gs inp b) := by
            have h1' : wVal gs1 inp v = wVal gsB inp v := hextB1.wVal_eq inp (by dsimp only [v]; omega)
            rw [h1', hB.2, hA.1 a ha, hA.1 b hb]
          have hsub : ∀ w ∈ as', wVal gsB inp w = wVal gs inp w := fun w hw =>
            hext0B.wVal_eq inp (by have := hasW w (by simp [hw]); omega)
          have hsubB : ∀ w ∈ bs', wVal gsB inp w = wVal gs inp w := fun w hw =>
            hext0B.wVal_eq inp (by have := hbsW w (by simp [hw]); omega)
          constructor
          · rw [List.map_cons, hu_val, h1.1, List.ofFn_succ]
            congr 1
            apply List.ext_getElem (by simp)
            intro i hi1 hi2
            have hik : i < k := by simp at hi1; exact hi1
            simp only [List.getElem_ofFn]
            have ha_mem : as'.getD i 0 ∈ as' := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            have hb_mem : bs'.getD i 0 ∈ bs' := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            rw [hsub _ ha_mem, hsubB _ hb_mem]
            simp [List.getD_eq_getElem?_getD]
          · rw [List.map_cons, hv_val, h1.2, List.ofFn_succ]
            congr 1
            apply List.ext_getElem (by simp)
            intro i hi1 hi2
            have hik : i < k := by simp at hi1; exact hi1
            simp only [List.getElem_ofFn]
            have ha_mem : as'.getD i 0 ∈ as' := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            have hb_mem : bs'.getD i 0 ∈ bs' := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            rw [hsub _ ha_mem, hsubB _ hb_mem]
            simp [List.getD_eq_getElem?_getD]
        · intro gs2 cHi cLo hext12 hgs2 hcH hcL hcHW hcLW
          cases cHi with
          | nil => simp at hcH
          | cons ub cHi' =>
            cases cLo with
            | nil => simp at hcL
            | cons vb cLo' =>
              simp only [List.length_cons, Nat.add_right_cancel_iff] at hcH hcL
              have hub : ub < m + gs2.length := hcHW ub (by simp)
              have hvb : vb < m + gs2.length := hcLW vb (by simp)
              have hext02 : Extends gs gs2 := hext01.trans hext12
              have ha2 : a < m + gs2.length := by have := hext02.length_le; omega
              have hb2 : b < m + gs2.length := by have := hext02.length_le; omega

              obtain ⟨hg1, hn1, hl1, ht1, he1⟩ := mkAnd_step hgs2 hb2 hvb
              let g1 := gs2 ++ [⟨GateOp.and, [b, vb]⟩]
              let t1 := m + gs2.length
              have hg1l : g1.length = gs2.length + 1 := hl1
              obtain ⟨hg2, hn2, hl2, habar, he2⟩ := mkOr_step hg1 (by omega : ub < m + g1.length) ht1
              let g2 := g1 ++ [⟨GateOp.or, [ub, t1]⟩]
              let abar := m + g1.length
              have hg2l : g2.length = g1.length + 1 := hl2
              obtain ⟨hg3, hn3, hl3, ht2, he3⟩ := mkAnd_step hg2 (by omega : a < m + g2.length) (by omega : vb < m + g2.length)
              let g3 := g2 ++ [⟨GateOp.and, [a, vb]⟩]
              let t2 := m + g2.length
              have hg3l : g3.length = g2.length + 1 := hl3
              obtain ⟨hg4, hn4, hl4, hbbar, he4⟩ := mkOr_step hg3 (by omega : ub < m + g3.length) ht2
              let g4 := g3 ++ [⟨GateOp.or, [ub, t2]⟩]
              let bbar := m + g3.length
              have hg4l : g4.length = g3.length + 1 := hl4
              have hext24 : Extends gs2 g4 :=
                Extends.trans ⟨_, rfl⟩ (Extends.trans ⟨_, rfl⟩ (Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩))
              have hlen24 : g4.length = gs2.length + 4 := by omega
              obtain ⟨gs3, rA', rB', hext43, hgs3, hnc3, hlen3, hrAl, hrBl, hrAW, hrBW, hev3⟩ :=
                hrev1 g4 cHi' cLo' (hext12.trans hext24) hg4 hcH hcL
                  (fun w hw => by have := hcHW w (by simp [hw]); omega)
                  (fun w hw => by have := hcLW w (by simp [hw]); omega)
              have hext23 : Extends gs2 gs3 := hext24.trans hext43
              have habar3 : abar < m + gs3.length := by have := hext43.length_le; dsimp only [abar]; omega
              have hbbar3 : bbar < m + gs3.length := by have := hext43.length_le; dsimp only [bbar]; omega
              have hnc23 : notCnt gs3 = notCnt gs2 := by rw [hnc3]; exact hn4.trans (hn3.trans (hn2.trans hn1))
              refine ⟨gs3, abar :: rA', bbar :: rB', hext23, hgs3, hnc23, by omega,
                by simp [hrAl], by simp [hrBl],
                fun w hw => by simp at hw; rcases hw with rfl | hw; exact habar3; exact hrAW w hw,
                fun w hw => by simp at hw; rcases hw with rfl | hw; exact hbbar3; exact hrBW w hw,
                ?_⟩
              intro inp hinp hcHiEq hcLoEq
              simp only [List.map_cons, List.cons.injEq] at hcHiEq hcLoEq
              have hA := hevalA inp hinp
              have hB := hevalB inp hinp
              have hu_val : wVal gs1 inp u = (wVal gs inp a || wVal gs inp b) := by
                rw [hextB1.wVal_eq inp (by dsimp only [u]; omega), hB.1 u (by dsimp only [u]; omega), hA.2]
              have hv_val : wVal gs1 inp v = (wVal gs inp a && wVal gs inp b) := by
                rw [hextB1.wVal_eq inp (by dsimp only [v]; omega), hB.2, hA.1 a ha, hA.1 b hb]
              have hub_val : wVal gs2 inp ub = !(wVal gs inp a || wVal gs inp b) := by
                rw [hcHiEq.1, hu_val]
              have hvb_val : wVal gs2 inp vb = !(wVal gs inp a && wVal gs inp b) := by
                rw [hcLoEq.1, hv_val]
              have ha_val2 : wVal gs2 inp a = wVal gs inp a := hext02.wVal_eq inp (by omega)
              have hb_val2 : wVal gs2 inp b = wVal gs inp b := hext02.wVal_eq inp (by omega)
              have hE1 := he1 inp hinp; have hE2 := he2 inp hinp
              have hE3 := he3 inp hinp; have hE4 := he4 inp hinp
              have habar_val : wVal gs3 inp abar = !(wVal gs inp a) := by
                rw [hext43.wVal_eq inp (by dsimp only [abar]; omega),
                  hE4.1 abar (by dsimp only [abar]; omega), hE3.1 abar (by dsimp only [abar]; omega),
                  hE2.2, hE1.1 ub (by omega), hE1.2, hub_val, hvb_val, hb_val2]
                exact (rev_comp_eq _ _).1
              have hbbar_val : wVal gs3 inp bbar = !(wVal gs inp b) := by
                rw [hext43.wVal_eq inp (by dsimp only [bbar]; omega), hE4.2,
                  hE3.1 ub (by omega), hE2.1 ub (by omega), hE1.1 ub (by omega),
                  hE3.2, hE2.1 a (by omega), hE1.1 a (by omega),
                  hE2.1 vb (by omega), hE1.1 vb (by omega),
                  hub_val, hvb_val, ha_val2]
                exact (rev_comp_eq _ _).2
              have hcHi4 : cHi'.map (wVal g4 inp) = (hi'.map (wVal gs1 inp)).map (!·) := by
                rw [hext24.map_wVal_eq inp cHi' (fun w hw => by have := hcHW w (by simp [hw]); omega)]
                exact hcHiEq.2
              have hcLo4 : cLo'.map (wVal g4 inp) = (lo'.map (wVal gs1 inp)).map (!·) := by
                rw [hext24.map_wVal_eq inp cLo' (fun w hw => by have := hcLW w (by simp [hw]); omega)]
                exact hcLoEq.2
              have hsub3 := hev3 inp hinp hcHi4 hcLo4
              have hmapA : as'.map (wVal gsB inp) = as'.map (wVal gs inp) :=
                hext0B.map_wVal_eq inp as' (fun w hw => by have := hasW w (by simp [hw]); omega)
              have hmapB : bs'.map (wVal gsB inp) = bs'.map (wVal gs inp) :=
                hext0B.map_wVal_eq inp bs' (fun w hw => by have := hbsW w (by simp [hw]); omega)
              rw [hmapA, hmapB] at hsub3
              exact ⟨by rw [List.map_cons, List.map_cons, List.map_cons, habar_val, hsub3.1],
                     by rw [List.map_cons, List.map_cons, List.map_cons, hbbar_val, hsub3.2]⟩

lemma exists_bm {m : ℕ} : ∀ (k : ℕ) (gs : List Gate) (ws : List ℕ),
    GateOK m gs → ws.length = 2 ^ k → (∀ w ∈ ws, w < m + gs.length) →
    ∃ (gs1 : List Gate) (ys : List ℕ),
      Extends gs gs1 ∧ GateOK m gs1 ∧ notCnt gs1 = notCnt gs ∧
      gs1.length ≤ gs.length + k * 2 ^ k ∧
      ys.length = 2 ^ k ∧ (∀ w ∈ ys, w < m + gs1.length) ∧
      (∀ inp : List Bool, inp.length = m → IsBitonic (ws.map (wVal gs inp)) →
        IsSortedDesc (ys.map (wVal gs1 inp)) ∧
        (ys.map (wVal gs1 inp)).count true = (ws.map (wVal gs inp)).count true) ∧
      (∀ (gs2 : List Gate) (cs : List ℕ),
        Extends gs1 gs2 → GateOK m gs2 → cs.length = 2 ^ k → (∀ w ∈ cs, w < m + gs2.length) →
        ∃ (gs3 : List Gate) (rs : List ℕ),
          Extends gs2 gs3 ∧ GateOK m gs3 ∧ notCnt gs3 = notCnt gs2 ∧
          gs3.length ≤ gs2.length + 2 * k * 2 ^ k ∧
          rs.length = 2 ^ k ∧ (∀ w ∈ rs, w < m + gs3.length) ∧
          ∀ inp : List Bool, inp.length = m →
            cs.map (wVal gs2 inp) = (ys.map (wVal gs1 inp)).map (!·) →
            rs.map (wVal gs3 inp) = (ws.map (wVal gs inp)).map (!·)) := by
  intro k
  induction k with
  | zero =>
    intro gs ws hgs hwl hwsW
    refine ⟨gs, ws, Extends.refl gs, hgs, rfl, by simp, hwl, hwsW, ?_, ?_⟩
    · intro inp _ _
      cases ws with
      | nil => simp at hwl
      | cons w ws' =>
        cases ws' with
        | nil =>
          refine ⟨?_, rfl⟩
          cases h : wVal gs inp w <;> simp [IsSortedDesc, h]
        | cons _ _ => simp at hwl
    · intro gs2 cs _ hgs2 hcsl hcsW
      exact ⟨gs2, cs, Extends.refl gs2, hgs2, rfl, by simp, hcsl, hcsW, fun inp _ h => h⟩
  | succ k ih =>
    intro gs ws hgs hwl hwsW
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    let h := 2 ^ k
    let wsL := ws.take h
    let wsR := ws.drop h
    have hwsEq : ws = wsL ++ wsR := (List.take_append_drop h ws).symm
    have hLlen : wsL.length = h := by simp [wsL, hwl, hpow, h]
    have hRlen : wsR.length = h := by simp [wsR, hwl, hpow, h]
    obtain ⟨gsA, hi, lo, hext0A, hgsA, hncA, hlenA, hhil, hlol, hhiW, hloW, hevA, hrevA⟩ :=
      exists_comp_layer h gs wsL wsR hgs hLlen hRlen
        (fun w hw => hwsW w (List.mem_of_mem_take hw))
        (fun w hw => hwsW w (List.mem_of_mem_drop hw))
    obtain ⟨gsB, yHi, hextAB, hgsB, hncB, hlenB, hyHil, hyHiW, hevB, hrevB⟩ :=
      ih gsA hi hgsA hhil hhiW
    obtain ⟨gsC, yLo, hextBC, hgsC, hncC, hlenC, hyLol, hyLoW, hevC, hrevC⟩ :=
      ih gsB lo hgsB hlol (fun w hw => by have := hextAB.length_le; have := hloW w hw; omega)
    have hext0C : Extends gs gsC := hext0A.trans (hextAB.trans hextBC)
    have hlenC_bound : gsC.length ≤ gs.length + (k + 1) * 2 ^ (k + 1) := by
      have h1 : (k + 1) * 2 ^ (k + 1) = 2 * h + k * 2 ^ k + k * 2 ^ k := by dsimp only [h]; ring
      omega
    refine ⟨gsC, yHi ++ yLo, hext0C, hgsC, by omega, hlenC_bound,
      by simp [hyHil, hyLol, hpow],
      fun w hw => by
        simp only [List.mem_append] at hw
        rcases hw with hw | hw
        · have := hextBC.length_le; have := hyHiW w hw; omega
        · exact hyLoW w hw,
      ?_, ?_⟩
    · intro inp hinp hBit
      let L := ws.map (wVal gs inp)
      have hLlen' : L.length = 2 * h := by simp [L, hwl, hpow, h]; omega
      have hA := hevA inp hinp
      have hhiEq : hi.map (wVal gsA inp) =
          List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false) := by
        rw [hA.1]
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        have hih : i < h := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn]
        have h1 : wVal gs inp (wsL.getD i 0) = L.getD i false := by
          simp only [List.getD_eq_getElem?_getD, L, wsL]
          rw [List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega),
              List.getElem?_eq_getElem (by simp [hwl, hpow]; omega)]
          simp
        have h2 : wVal gs inp (wsR.getD i 0) = L.getD (i + h) false := by
          simp only [List.getD_eq_getElem?_getD, L, wsR]
          rw [List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega),
              List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega)]
          simp [Nat.add_comm]
        rw [h1, h2]
      have hloEq : lo.map (wVal gsA inp) =
          List.ofFn (fun i : Fin h => L.getD i.1 false && L.getD (i.1 + h) false) := by
        rw [hA.2]
        apply List.ext_getElem (by simp)
        intro i hi1 hi2
        have hih : i < h := by simp at hi1; exact hi1
        simp only [List.getElem_ofFn]
        have h1 : wVal gs inp (wsL.getD i 0) = L.getD i false := by
          simp only [List.getD_eq_getElem?_getD, L, wsL]
          rw [List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega),
              List.getElem?_eq_getElem (by simp [hwl, hpow]; omega)]
          simp
        have h2 : wVal gs inp (wsR.getD i 0) = L.getD (i + h) false := by
          simp only [List.getD_eq_getElem?_getD, L, wsR]
          rw [List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega),
              List.getElem?_eq_getElem (by simp [hwl, hpow, h]; omega)]
          simp [Nat.add_comm]
        rw [h1, h2]
      have hlay := bitonic_layer hLlen' hBit
      have hloB : lo.map (wVal gsB inp) = lo.map (wVal gsA inp) :=
        hextAB.map_wVal_eq inp lo (fun w hw => by have := hloW w hw; omega)
      have hB := hevB inp hinp (by rw [hhiEq]; exact hlay.1)
      have hC := hevC inp hinp (by rw [hloB, hloEq]; exact hlay.2.1)
      have hyHiC : yHi.map (wVal gsC inp) = yHi.map (wVal gsB inp) :=
        hextBC.map_wVal_eq inp yHi (fun w hw => by have := hyHiW w hw; omega)
      have hcntTot : (yHi.map (wVal gsB inp)).count true + (yLo.map (wVal gsC inp)).count true =
          L.count true := by
        rw [hB.2, hC.2, hloB, hhiEq, hloEq]
        exact count_true_ofFn_or_and h L hLlen'
      rw [List.map_append, hyHiC]
      refine ⟨?_, by rw [List.count_append]; exact hcntTot⟩
      apply isSortedDesc_append_of_const hB.1 hC.1
      rcases hlay.2.2 with hloF | hhiT
      · left
        have hcnt0 : (yLo.map (wVal gsC inp)).count true = 0 := by
          rw [hC.2, hloB, hloEq, List.count_eq_zero]
          intro hm; exact Bool.noConfusion (hloF true hm)
        intro x hx
        cases x
        · rfl
        · exfalso; exact (List.count_eq_zero.1 hcnt0) hx
      · right
        have hcntH : (yHi.map (wVal gsB inp)).count true = (yHi.map (wVal gsB inp)).length := by
          rw [hB.2, hhiEq, List.length_map, hyHil]
          have hc : (List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false)).count true = h := by
            have hall : List.ofFn (fun i : Fin h => L.getD i.1 false || L.getD (i.1 + h) false) = List.replicate h true := by
              apply List.ext_getElem (by simp)
              intro i hi1 hi2
              simp only [List.getElem_replicate]
              exact hhiT _ (List.getElem_mem hi1)
            rw [hall]; simp
          exact hc
        intro x hx
        cases x
        · exfalso
          have h1 := hB.1
          unfold IsSortedDesc at h1
          rw [hcntH, Nat.sub_self, List.replicate_zero, List.append_nil] at h1
          rw [h1] at hx; simp at hx
        · rfl
    · intro gs2 cs hextC2 hgs2 hcsl hcsW
      let cHi := cs.take h
      let cLo := cs.drop h
      have hcHil : cHi.length = h := by simp [cHi, hcsl, hpow, h]
      have hcLol : cLo.length = h := by simp [cLo, hcsl, hpow, h]
      obtain ⟨gs3, rHi, hext23, hgs3, hnc3, hlen3, hrHil, hrHiW, hev3⟩ :=
        hrevB gs2 cHi (hextBC.trans hextC2) hgs2 hcHil
          (fun w hw => hcsW w (List.mem_of_mem_take hw))
      obtain ⟨gs4, rLo, hext34, hgs4, hnc4, hlen4, hrLol, hrLoW, hev4⟩ :=
        hrevC gs3 cLo (hextC2.trans hext23) hgs3 hcLol
          (fun w hw => by have := hext23.length_le; have := hcsW w (List.mem_of_mem_drop hw); omega)
      obtain ⟨gs5, rL, rR, hext45, hgs5, hnc5, hlen5, hrLl, hrRl, hrLW, hrRW, hev5⟩ :=
        hrevA gs4 rHi rLo (hextAB.trans (hextBC.trans (hextC2.trans (hext23.trans hext34)))) hgs4 hrHil hrLol
          (fun w hw => by have := hext34.length_le; have := hrHiW w hw; omega)
          hrLoW
      have hext25 : Extends gs2 gs5 := hext23.trans (hext34.trans hext45)
      have hlen5_bound : gs5.length ≤ gs2.length + 2 * (k + 1) * 2 ^ (k + 1) := by
        have h1 : 2 * (k + 1) * 2 ^ (k + 1) = 4 * h + 2 * k * 2 ^ k + 2 * k * 2 ^ k := by dsimp only [h]; ring
        omega
      refine ⟨gs5, rL ++ rR, hext25, hgs5, by omega, hlen5_bound,
        by simp [hrLl, hrRl, hpow, h],
        fun w hw => by
          simp only [List.mem_append] at hw
          rcases hw with hw | hw
          · exact hrLW w hw
          · exact hrRW w hw,
        ?_⟩
      intro inp hinp hcsEq
      rw [List.map_append, List.map_append] at hcsEq
      have hcsEq2 : cHi.map (wVal gs2 inp) ++ cLo.map (wVal gs2 inp) =
          (yHi.map (wVal gsC inp)).map (!·) ++ (yLo.map (wVal gsC inp)).map (!·) := by
        rw [← List.map_append, List.take_append_drop]; exact hcsEq
      have hspl := List.append_inj hcsEq2 (by simp [hcHil, hyHil, h])
      have hyHiC : yHi.map (wVal gsC inp) = yHi.map (wVal gsB inp) :=
        hextBC.map_wVal_eq inp yHi (fun w hw => by have := hyHiW w hw; omega)
      have hrHiEq : rHi.map (wVal gs3 inp) = (hi.map (wVal gsA inp)).map (!·) :=
        hev3 inp hinp (by rw [← hyHiC]; exact hspl.1)
      have hcLo3 : cLo.map (wVal gs3 inp) = (yLo.map (wVal gsC inp)).map (!·) := by
        rw [hext23.map_wVal_eq inp cLo (fun w hw => by have := hcsW w (List.mem_of_mem_drop hw); omega)]
        exact hspl.2
      have hrLoEq : rLo.map (wVal gs4 inp) = (lo.map (wVal gsA inp)).map (!·) := by
        have h := hev4 inp hinp hcLo3
        rw [hextAB.map_wVal_eq inp lo (fun w hw => by have := hloW w hw; omega)] at h
        exact h
      have hrHi4 : rHi.map (wVal gs4 inp) = (hi.map (wVal gsA inp)).map (!·) := by
        rw [hext34.map_wVal_eq inp rHi (fun w hw => by have := hrHiW w hw; omega)]
        exact hrHiEq
      have h5 := hev5 inp hinp hrHi4 hrLoEq
      rw [List.map_append, h5.1, h5.2, ← List.map_append, ← List.map_append, List.take_append_drop]

lemma win_merge_step (K m A B t : ℕ) (ht : t < m) (hB : B ≤ m) :
    let cA := if K ≤ A then 2 * m else if A + 2 * m ≤ K then 0 else A + 2 * m - K
    decide (m + t < cA + B) = decide (K + 1 + t ≤ A + B + m) := by
  dsimp only
  split_ifs <;> simp only [decide_eq_decide] <;> omega

lemma count_win_spec (K s A : ℕ) (L : List Bool) (hL : L.length = s)
    (hget : ∀ (t : ℕ) (ht : t < s), L[t]'(by omega) = decide (K + 1 + t ≤ A + s)) :
    IsSortedDesc L ∧
    L.count true = if K ≤ A then s else if A + s ≤ K then 0 else A + s - K := by
  let c := if K ≤ A then s else if A + s ≤ K then 0 else A + s - K
  have hc_le : c ≤ s := by dsimp only [c]; split_ifs <;> omega
  have hiff : ∀ t < s, (K + 1 + t ≤ A + s) ↔ t < c := by
    intro t ht; dsimp only [c]; split_ifs <;> omega
  have hEq : L = List.replicate c true ++ List.replicate (s - c) false := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      rw [hget i (by omega)]
      by_cases hic : i < c
      · rw [List.getElem_append_left (by simp [hic])]
        simp [(hiff i (by omega)).2 hic]
      · rw [List.getElem_append_right (by simp; omega)]
        simp [show ¬ (K + 1 + i ≤ A + s) from fun h => hic ((hiff i (by omega)).1 h)]
  have hcnt : L.count true = c := by rw [hEq]; simp [List.count_replicate]
  refine ⟨?_, hcnt⟩
  unfold IsSortedDesc
  rw [hcnt, hL]; exact hEq

lemma exists_sort_full {m : ℕ} (wF : ℕ) (hwF : wF < m) : ∀ (k : ℕ) (gs : List Gate) (ws : List ℕ),
    GateOK m gs → ws.length = 2 ^ k → (∀ w ∈ ws, w < m + gs.length) →
    ∃ (gs1 : List Gate) (ys : List ℕ),
      Extends gs gs1 ∧ GateOK m gs1 ∧ notCnt gs1 = notCnt gs ∧
      gs1.length ≤ gs.length + k * (k + 1) * 2 ^ k ∧
      ys.length = 2 ^ k ∧ (∀ w ∈ ys, w < m + gs1.length) ∧
      (∀ inp : List Bool, inp.length = m →
        IsSortedDesc (ys.map (wVal gs1 inp)) ∧
        (ys.map (wVal gs1 inp)).count true = (ws.map (wVal gs inp)).count true) ∧
      (∀ (gs2 : List Gate) (cs : List ℕ),
        Extends gs1 gs2 → GateOK m gs2 → cs.length = 2 ^ k → (∀ w ∈ cs, w < m + gs2.length) →
        ∃ (gs3 : List Gate) (rs : List ℕ),
          Extends gs2 gs3 ∧ GateOK m gs3 ∧ notCnt gs3 = notCnt gs2 ∧
          gs3.length ≤ gs2.length + 2 * k * (k + 1) * 2 ^ k ∧
          rs.length = 2 ^ k ∧ (∀ w ∈ rs, w < m + gs3.length) ∧
          ∀ inp : List Bool, inp.length = m →
            cs.map (wVal gs2 inp) = (ys.map (wVal gs1 inp)).map (!·) →
            rs.map (wVal gs3 inp) = (ws.map (wVal gs inp)).map (!·)) ∧
      (∀ (K : ℕ) (gs2 : List Gate) (win : List ℕ),
        Extends gs1 gs2 → GateOK m gs2 → win.length = 2 ^ k → (∀ w ∈ win, w < m + gs2.length) →
        ∃ (gs3 : List Gate) (leaves : List ℕ),
          Extends gs2 gs3 ∧ GateOK m gs3 ∧ notCnt gs3 = notCnt gs2 ∧
          gs3.length ≤ gs2.length + 4 * k * (k + 2) * 2 ^ k ∧
          leaves.length = 2 ^ k ∧ (∀ w ∈ leaves, w < m + gs3.length) ∧
          ∀ (inp : List Bool) (A : ℕ), inp.length = m → inp.getD wF false = false →
            (∀ t < 2 ^ k, wVal gs2 inp (win.getD t 0) = decide (K + 1 + t ≤ A + 2 ^ k)) →
            ∀ j < 2 ^ k,
              wVal gs3 inp (leaves.getD j 0) =
              decide (K ≤ A + ((ws.map (wVal gs inp)).count true -
                if wVal gs inp (ws.getD j 0) then 1 else 0))) := by
  intro k
  induction k with
  | zero =>
    intro gs ws hgs hwl hwsW
    refine ⟨gs, ws, Extends.refl gs, hgs, rfl, by simp, hwl, hwsW, ?_, ?_, ?_⟩
    · intro inp _
      cases ws with
      | nil => simp at hwl
      | cons w ws' =>
        cases ws' with
        | nil => refine ⟨by cases h : wVal gs inp w <;> simp [IsSortedDesc, h], rfl⟩
        | cons _ _ => simp at hwl
    · intro gs2 cs _ hgs2 hcsl hcsW
      exact ⟨gs2, cs, Extends.refl gs2, hgs2, rfl, by simp, hcsl, hcsW, fun _ _ h => h⟩
    · intro K gs2 win _ hgs2 hwinl hwinW
      refine ⟨gs2, win, Extends.refl gs2, hgs2, rfl, by simp, hwinl, hwinW, ?_⟩
      intro inp A _ _ hwinSpec j hj
      have hj0 : j = 0 := by omega
      subst hj0
      have h0 := hwinSpec 0 (by omega)
      cases ws with
      | nil => simp at hwl
      | cons w ws' =>
        cases ws' with
        | nil =>
          rw [h0]
          cases h : wVal gs inp w <;> simp [h]
        | cons _ _ => simp at hwl
  | succ k ih =>
    intro gs ws hgs hwl hwsW
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    let h := 2 ^ k
    let wsL := ws.take h
    let wsR := ws.drop h
    have hLlen : wsL.length = h := by simp [wsL, hwl, hpow, h]
    have hRlen : wsR.length = h := by simp [wsR, hwl, hpow, h]
    obtain ⟨gsA, ysL, hext0A, hgsA, hncA, hlenA, hyLl, hyLW, hevA, hrevA, hwinA⟩ :=
      ih gs wsL hgs hLlen (fun w hw => hwsW w (List.mem_of_mem_take hw))
    obtain ⟨gsB, ysR, hextAB, hgsB, hncB, hlenB, hyRl, hyRW, hevB, hrevB, hwinB⟩ :=
      ih gsA wsR hgsA hRlen
        (fun w hw => by have := hext0A.length_le; have := hwsW w (List.mem_of_mem_drop hw); omega)
    obtain ⟨gsC, ys, hextBC, hgsC, hncC, hlenC, hysl, hysW, hevC, hrevC⟩ :=
      exists_bm (k + 1) gsB (ysL ++ ysR.reverse) hgsB
        (by simp [hyLl, hyRl, hpow])
        (fun w hw => by
          simp only [List.mem_append, List.mem_reverse] at hw
          rcases hw with hw | hw
          · have := hextAB.length_le; have := hyLW w hw; omega
          · exact hyRW w hw)
    have hext0B : Extends gs gsB := hext0A.trans hextAB
    have hext0C : Extends gs gsC := hext0B.trans hextBC
    have hlenC_bound : gsC.length ≤ gs.length + (k + 1) * (k + 2) * 2 ^ (k + 1) := by
      have h1 : (k + 1) * (k + 2) * 2 ^ (k + 1) =
          k * (k + 1) * 2 ^ k + k * (k + 1) * 2 ^ k + (k + 1) * 2 ^ (k + 1) + 2 * (k + 1) * 2 ^ k := by
        ring
      omega
    refine ⟨gsC, ys, hext0C, hgsC, by omega, hlenC_bound, hysl, hysW, ?_, ?_, ?_⟩
    · intro inp hinp
      have hA := hevA inp hinp
      have hB := hevB inp hinp
      have hwsRA : wsR.map (wVal gsA inp) = wsR.map (wVal gs inp) :=
        hext0A.map_wVal_eq inp wsR (fun w hw => by have := hwsW w (List.mem_of_mem_drop hw); omega)
      have hyLB : ysL.map (wVal gsB inp) = ysL.map (wVal gsA inp) :=
        hextAB.map_wVal_eq inp ysL (fun w hw => by have := hyLW w hw; omega)
      have hBit : IsBitonic ((ysL ++ ysR.reverse).map (wVal gsB inp)) := by
        rw [List.map_append, List.map_reverse, hyLB]
        exact isBitonic_of_sorted_append_rev hA.1 hB.1
      have hC := hevC inp hinp hBit
      refine ⟨hC.1, ?_⟩
      rw [hC.2, List.map_append, List.map_reverse, hyLB, List.count_append, List.count_reverse,
        hA.2, hB.2, hwsRA, ← List.count_append, ← List.map_append, List.take_append_drop]
    · intro gs2 cs hextC2 hgs2 hcsl hcsW
      obtain ⟨gs3, cBit, hext23, hgs3, hnc3, hlen3, hcBitl, hcBitW, hev3⟩ :=
        hrevC gs2 cs hextC2 hgs2 hcsl hcsW
      let cL := cBit.take h
      let cR := (cBit.drop h).reverse
      have hcLl : cL.length = h := by simp [cL, hcBitl, hpow, h]
      have hcRl : cR.length = h := by simp [cR, hcBitl, hpow, h]
      obtain ⟨gs4, rL, hext34, hgs4, hnc4, hlen4, hrLl, hrLW, hev4⟩ :=
        hrevA gs3 cL (hextAB.trans (hextBC.trans (hextC2.trans hext23))) hgs3 hcLl
          (fun w hw => hcBitW w (List.mem_of_mem_take hw))
      obtain ⟨gs5, rR, hext45, hgs5, hnc5, hlen5, hrRl, hrRW, hev5⟩ :=
        hrevB gs4 cR (hextBC.trans (hextC2.trans (hext23.trans hext34))) hgs4 hcRl
          (fun w hw => by
            have := hext34.length_le
            have := hcBitW w (List.mem_of_mem_drop (List.mem_reverse.1 hw)); omega)
      have hext25 : Extends gs2 gs5 := hext23.trans (hext34.trans hext45)
      have hlen5_bound : gs5.length ≤ gs2.length + 2 * (k + 1) * (k + 2) * 2 ^ (k + 1) := by
        have h1 : 2 * (k + 1) * (k + 2) * 2 ^ (k + 1) =
            2 * (k + 1) * 2 ^ (k + 1) + 2 * k * (k + 1) * 2 ^ k + 2 * k * (k + 1) * 2 ^ k +
            4 * (k + 1) * 2 ^ k := by
          ring
        omega
      refine ⟨gs5, rL ++ rR, hext25, hgs5, by omega, hlen5_bound,
        by simp [hrLl, hrRl, hpow],
        fun w hw => by
          simp only [List.mem_append] at hw
          rcases hw with hw | hw
          · have := hext45.length_le; have := hrLW w hw; omega
          · exact hrRW w hw,
        ?_⟩
      intro inp hinp hcsEq
      have h3 := hev3 inp hinp hcsEq
      rw [List.map_append, List.map_reverse, List.map_append, List.map_reverse] at h3
      have h3' : cL.map (wVal gs3 inp) ++ (cBit.drop h).map (wVal gs3 inp) =
          (ysL.map (wVal gsB inp)).map (!·) ++ ((ysR.map (wVal gsB inp)).map (!·)).reverse := by
        rw [← List.map_append, List.take_append_drop]; exact h3
      have hspl := List.append_inj h3' (by simp [hcLl, hyLl, h])
      have hyLB : ysL.map (wVal gsB inp) = ysL.map (wVal gsA inp) :=
        hextAB.map_wVal_eq inp ysL (fun w hw => by have := hyLW w hw; omega)
      have h4 := hev4 inp hinp (by rw [← hyLB]; exact hspl.1)
      have hcR4 : cR.map (wVal gs4 inp) = (ysR.map (wVal gsB inp)).map (!·) := by
        rw [hext34.map_wVal_eq inp cR (fun w hw => by
          have := hcBitW w (List.mem_of_mem_drop (List.mem_reverse.1 hw)); omega)]
        simp only [cR, List.map_reverse]
        rw [hspl.2, List.reverse_reverse]
      have h5 := hev5 inp hinp hcR4
      have hwsRA : wsR.map (wVal gsA inp) = wsR.map (wVal gs inp) :=
        hext0A.map_wVal_eq inp wsR (fun w hw => by have := hwsW w (List.mem_of_mem_drop hw); omega)
      rw [hwsRA] at h5
      have hrL5 : rL.map (wVal gs5 inp) = rL.map (wVal gs4 inp) :=
        hext45.map_wVal_eq inp rL (fun w hw => by have := hrLW w hw; omega)
      rw [List.map_append, hrL5, h4, h5, ← List.map_append, ← List.map_append, List.take_append_drop]
    · intro K gs2 win hextC2 hgs2 hwinl hwinW
      have hpow2 : 2 ^ (k + 2) = 2 ^ (k + 1) + 2 ^ (k + 1) := by ring
      have hextB2 : Extends gsB gs2 := hextBC.trans hextC2
      have hextA2 : Extends gsA gs2 := hextAB.trans hextB2
      let padR := ysR ++ List.replicate h wF
      let padL := ysL ++ List.replicate h wF
      have hpadRl : padR.length = 2 ^ (k + 1) := by simp [padR, hyRl, hpow, h]
      have hpadLl : padL.length = 2 ^ (k + 1) := by simp [padL, hyLl, hpow, h]

      obtain ⟨gs3, mL, hext23, hgs3, hnc3, hlen3, hmLl, hmLW, hev3, _⟩ :=
        exists_bm (k + 2) gs2 (win ++ padR.reverse) hgs2
          (by simp [hwinl, hpadRl, hpow2])
          (fun w hw => by
            simp only [List.mem_append, List.mem_reverse, padR, List.mem_replicate] at hw
            rcases hw with hw | (hw | ⟨_, rfl⟩)
            · exact hwinW w hw
            · have := hextB2.length_le; have := hyRW w hw; omega
            · omega)

      obtain ⟨gs4, mR, hext34, hgs4, hnc4, hlen4, hmRl, hmRW, hev4, _⟩ :=
        exists_bm (k + 2) gs3 (win ++ padL.reverse) hgs3
          (by simp [hwinl, hpadLl, hpow2])
          (fun w hw => by
            simp only [List.mem_append, List.mem_reverse, padL, List.mem_replicate] at hw
            rcases hw with hw | (hw | ⟨_, rfl⟩)
            · have := hext23.length_le; have := hwinW w hw; omega
            · have := hext23.length_le; have := hextA2.length_le; have := hyLW w hw; omega
            · omega)
      let winForL := (mL.drop h).take h
      let winForR := (mR.drop h).take h
      have hwfLl : winForL.length = h := by simp [winForL, hmLl, hpow2, hpow, h]; omega
      have hwfRl : winForR.length = h := by simp [winForR, hmRl, hpow2, hpow, h]; omega
      obtain ⟨gs5, leavesL, hext45, hgs5, hnc5, hlen5, hlLl, hlLW, hev5⟩ :=
        hwinA K gs4 winForL (hextA2.trans (hext23.trans hext34)) hgs4 hwfLl
          (fun w hw => by
            have := hext34.length_le
            have := hmLW w (List.mem_of_mem_drop (List.mem_of_mem_take hw)); omega)
      obtain ⟨gs6, leavesR, hext56, hgs6, hnc6, hlen6, hlRl, hlRW, hev6⟩ :=
        hwinB K gs5 winForR (hextB2.trans (hext23.trans (hext34.trans hext45))) hgs5 hwfRl
          (fun w hw => by
            have := hext45.length_le
            have := hmRW w (List.mem_of_mem_drop (List.mem_of_mem_take hw)); omega)
      have hext26 : Extends gs2 gs6 := hext23.trans (hext34.trans (hext45.trans hext56))
      have hlen6_bound : gs6.length ≤ gs2.length + 4 * (k + 1) * (k + 3) * 2 ^ (k + 1) := by
        have h1 : 4 * (k + 1) * (k + 3) * 2 ^ (k + 1) =
            (k + 2) * 2 ^ (k + 2) + (k + 2) * 2 ^ (k + 2) +
            4 * k * (k + 2) * 2 ^ k + 4 * k * (k + 2) * 2 ^ k + 8 * (k + 1) * 2 ^ k := by
          ring
        omega
      refine ⟨gs6, leavesL ++ leavesR, hext26, hgs6, by omega, hlen6_bound,
        by simp [hlLl, hlRl, hpow],
        fun w hw => by
          simp only [List.mem_append] at hw
          rcases hw with hw | hw
          · have := hext56.length_le; have := hlLW w hw; omega
          · exact hlRW w hw,
        ?_⟩
      intro inp A hinp hwFval hwinSpec j hj
      have hA_sort := hevA inp hinp
      have hB_sort := hevB inp hinp
      have hwsRA : wsR.map (wVal gsA inp) = wsR.map (wVal gs inp) :=
        hext0A.map_wVal_eq inp wsR (fun w hw => by have := hwsW w (List.mem_of_mem_drop hw); omega)
      have hcntW : (ws.map (wVal gs inp)).count true =
          (wsL.map (wVal gs inp)).count true + (wsR.map (wVal gs inp)).count true := by
        rw [← List.count_append, ← List.map_append, List.take_append_drop]
      have hwin_s := count_win_spec K (2 ^ (k + 1)) A (win.map (wVal gs2 inp)) (by simp [hwinl])
        (fun t ht => by
          have h1 := hwinSpec t ht
          simp only [List.getD_eq_getElem?_getD] at h1
          rw [List.getElem?_eq_getElem (by omega : t < win.length)] at h1
          simpa using h1)
      have hwF2 : wVal gs2 inp wF = false := by rw [evalWires_input gs2 inp (by omega), hwFval]
      have hwF3 : wVal gs3 inp wF = false := by rw [evalWires_input gs3 inp (by omega), hwFval]

      have hpadR_s : IsSortedDesc (padR.map (wVal gs2 inp)) ∧
          (padR.map (wVal gs2 inp)).count true = (wsR.map (wVal gs inp)).count true := by
        have hyR2 : ysR.map (wVal gs2 inp) = ysR.map (wVal gsB inp) :=
          hextB2.map_wVal_eq inp ysR (fun w hw => by have := hyRW w hw; omega)
        rw [List.map_append, hyR2, List.map_replicate, hwF2]
        refine ⟨isSortedDesc_append_of_const hB_sort.1
            (isSortedDesc_of_all_false (fun x hx => (List.mem_replicate.1 hx).2))
            (Or.inl (fun x hx => (List.mem_replicate.1 hx).2)), ?_⟩
        simp [List.count_replicate, hB_sort.2, hwsRA]
      have hmL_s := hev3 inp hinp (by
        rw [List.map_append, List.map_reverse]
        exact isBitonic_of_sorted_append_rev hwin_s.1 hpadR_s.1)
      have hmL_cnt : (mL.map (wVal gs3 inp)).count true =
          (if K ≤ A then 2 * h else if A + 2 * h ≤ K then 0 else A + 2 * h - K) +
          (wsR.map (wVal gs inp)).count true := by
        rw [hmL_s.2, List.map_append, List.map_reverse, List.count_append, List.count_reverse,
          hwin_s.2, hpadR_s.2]
        have : 2 ^ (k + 1) = 2 * h := by dsimp only [h]; ring
        rw [this]
      have hwfL_spec : ∀ t < h,
          wVal gs4 inp (winForL.getD t 0) =
          decide (K + 1 + t ≤ (A + (wsR.map (wVal gs inp)).count true) + h) := by
        intro t ht
        have hgt : winForL.getD t 0 = mL[h + t]'(by omega) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < winForL.length)]
          simp [winForL, List.getElem_take, List.getElem_drop]
        rw [hgt]
        have hwmem : mL[h + t]'(by omega) ∈ mL := List.getElem_mem _
        rw [hext34.wVal_eq inp (by have := hmLW _ hwmem; omega)]
        have hgetM := getElem_isSortedDesc hmL_s.1 (i := h + t) (by simp [hmLl, hpow2, hpow, h]; omega)
        simp only [List.getElem_map] at hgetM
        rw [hgetM, hmL_cnt]
        have hBle : (wsR.map (wVal gs inp)).count true ≤ h := by
          have := count_true_le_length (wsR.map (wVal gs inp)); simpa [hRlen] using this
        exact win_merge_step K h A _ t ht hBle

      have hwin3 : win.map (wVal gs3 inp) = win.map (wVal gs2 inp) :=
        hext23.map_wVal_eq inp win (fun w hw => by have := hwinW w hw; omega)
      have hpadL_s : IsSortedDesc (padL.map (wVal gs3 inp)) ∧
          (padL.map (wVal gs3 inp)).count true = (wsL.map (wVal gs inp)).count true := by
        have hyL3 : ysL.map (wVal gs3 inp) = ysL.map (wVal gsA inp) :=
          (hextA2.trans hext23).map_wVal_eq inp ysL (fun w hw => by have := hyLW w hw; omega)
        rw [List.map_append, hyL3, List.map_replicate, hwF3]
        refine ⟨isSortedDesc_append_of_const hA_sort.1
            (isSortedDesc_of_all_false (fun x hx => (List.mem_replicate.1 hx).2))
            (Or.inl (fun x hx => (List.mem_replicate.1 hx).2)), ?_⟩
        simp [List.count_replicate, hA_sort.2]
      have hmR_s := hev4 inp hinp (by
        rw [List.map_append, List.map_reverse, hwin3]
        exact isBitonic_of_sorted_append_rev hwin_s.1 hpadL_s.1)
      have hmR_cnt : (mR.map (wVal gs4 inp)).count true =
          (if K ≤ A then 2 * h else if A + 2 * h ≤ K then 0 else A + 2 * h - K) +
          (wsL.map (wVal gs inp)).count true := by
        rw [hmR_s.2, List.map_append, List.map_reverse, hwin3, List.count_append, List.count_reverse,
          hwin_s.2, hpadL_s.2]
        have : 2 ^ (k + 1) = 2 * h := by dsimp only [h]; ring
        rw [this]
      have hwfR_spec : ∀ t < h,
          wVal gs5 inp (winForR.getD t 0) =
          decide (K + 1 + t ≤ (A + (wsL.map (wVal gs inp)).count true) + h) := by
        intro t ht
        have hgt : winForR.getD t 0 = mR[h + t]'(by omega) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : t < winForR.length)]
          simp [winForR, List.getElem_take, List.getElem_drop]
        rw [hgt]
        have hwmem : mR[h + t]'(by omega) ∈ mR := List.getElem_mem _
        rw [hext45.wVal_eq inp (by have := hmRW _ hwmem; omega)]
        have hgetM := getElem_isSortedDesc hmR_s.1 (i := h + t) (by simp [hmRl, hpow2, hpow, h]; omega)
        simp only [List.getElem_map] at hgetM
        rw [hgetM, hmR_cnt]
        have hBle : (wsL.map (wVal gs inp)).count true ≤ h := by
          have := count_true_le_length (wsL.map (wVal gs inp)); simpa [hLlen] using this
        exact win_merge_step K h A _ t ht hBle
      by_cases hjh : j < h
      · have hgetL : (leavesL ++ leavesR).getD j 0 = leavesL.getD j 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < leavesL.length)]
        rw [hgetL]
        have hmemL : leavesL.getD j 0 ∈ leavesL := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        rw [hext56.wVal_eq inp (by have := hlLW _ hmemL; omega)]
        rw [hev5 inp (A + (wsR.map (wVal gs inp)).count true) hinp hwFval hwfL_spec j hjh]
        have hwsj : wsL.getD j 0 = ws.getD j 0 := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_getElem (by omega : j < wsL.length),
              List.getElem?_eq_getElem (by omega : j < ws.length)]
          simp [wsL, List.getElem_take]
        rw [hwsj, hcntW]
        have h1 : (if wVal gs inp (ws.getD j 0) then 1 else 0) ≤ (wsL.map (wVal gs inp)).count true := by
          cases hb : wVal gs inp (ws.getD j 0)
          · simp
          · simp only [↓reduceIte]
            have hmemL' : wsL.getD j 0 ∈ wsL := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            have hmem : true ∈ wsL.map (wVal gs inp) := by
              rw [← hb, ← hwsj]; exact List.mem_map_of_mem hmemL'
            exact List.count_pos_iff.2 hmem
        simp only [decide_eq_decide]; omega
      · have hgetR : (leavesL ++ leavesR).getD j 0 = leavesR.getD (j - h) 0 := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : leavesL.length ≤ j)]
          congr 2; omega
        rw [hgetR]
        rw [hev6 inp (A + (wsL.map (wVal gs inp)).count true) hinp hwFval hwfR_spec (j - h) (by omega)]
        have hwsj : wsR.getD (j - h) 0 = ws.getD j 0 := by
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_eq_getElem (by omega : j - h < wsR.length),
              List.getElem?_eq_getElem (by omega : j < ws.length)]
          simp only [wsR, List.getElem_drop, Option.getD_some]
          congr 1; omega
        rw [hwsj, hwsRA, hcntW]
        have hmem_ws : ws.getD j 0 ∈ ws := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have hwr : wVal gsA inp (ws.getD j 0) = wVal gs inp (ws.getD j 0) :=
          hext0A.wVal_eq inp (by have := hwsW _ hmem_ws; omega)
        rw [hwr]
        have h1 : (if wVal gs inp (ws.getD j 0) then 1 else 0) ≤ (wsR.map (wVal gs inp)).count true := by
          cases hb : wVal gs inp (ws.getD j 0)
          · simp
          · simp only [↓reduceIte]
            have hmemR' : wsR.getD (j - h) 0 ∈ wsR := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
            have hmem : true ∈ wsR.map (wVal gs inp) := by
              rw [← hb, ← hwsj]; exact List.mem_map_of_mem hmemR'
            exact List.count_pos_iff.2 hmem
        simp only [decide_eq_decide]; omega

def inpVec (m : ℕ) (x : Finset (Fin m)) : List Bool :=
  List.ofFn (fun i : Fin m => decide (i ∈ x)) ++ [false, true]

lemma inpVec_length (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).length = m + 2 := by
  simp [inpVec]

lemma inpVec_getD_lt (m : ℕ) (x : Finset (Fin m)) (i : Fin m) :
    (inpVec m x).getD i.val false = decide (i ∈ x) := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by simp : i.val < (List.ofFn (fun j : Fin m => decide (j ∈ x))).length)]
  rw [List.getElem?_eq_getElem (by simp)]
  simp

lemma inpVec_getD_m (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).getD m false = false := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp : (List.ofFn (fun j : Fin m => decide (j ∈ x))).length ≤ m)]
  simp

lemma inpVec_getD_m1 (m : ℕ) (x : Finset (Fin m)) : (inpVec m x).getD (m + 1) false = true := by
  simp only [inpVec, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by simp : (List.ofFn (fun j : Fin m => decide (j ∈ x))).length ≤ m + 1)]
  simp

lemma exists_map_build {m : ℕ} (c len : ℕ) (gs0 : List Gate) (P : ℕ → List Gate → ℕ → Prop)
    (hP_mono : ∀ i < len, ∀ gs1 gs2 w, w < m + gs1.length → Extends gs1 gs2 → P i gs1 w → P i gs2 w)
    (hstep : ∀ i < len, ∀ gs, Extends gs0 gs → GateOK m gs →
      ∃ gs' w, Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + c ∧ w < m + gs'.length ∧ P i gs' w)
    (hgs0 : GateOK m gs0) :
    ∃ (gs' : List Gate) (ws : List ℕ),
      Extends gs0 gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs0 ∧
      gs'.length ≤ gs0.length + c * len ∧ ws.length = len ∧
      (∀ w ∈ ws, w < m + gs'.length) ∧
      ∀ i < len, P i gs' (ws.getD i 0) := by
  suffices h : ∀ k ≤ len,
      ∃ (gs' : List Gate) (ws : List ℕ),
        Extends gs0 gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs0 ∧
        gs'.length ≤ gs0.length + c * k ∧ ws.length = k ∧
        (∀ w ∈ ws, w < m + gs'.length) ∧
        ∀ i < k, P i gs' (ws.getD i 0) from h len le_rfl
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨gs0, [], Extends.refl gs0, hgs0, rfl, by simp, rfl, by simp, fun i hi => by omega⟩
  | succ k ih =>
    intro hk
    obtain ⟨gs1, ws1, hext01, hgs1, hnc1, hlen1, hwl1, hwsW1, hP1⟩ := ih (by omega)
    obtain ⟨gs2, wk, hext12, hgs2, hnc2, hlen2, hwk, hPk⟩ := hstep k (by omega) gs1 hext01 hgs1
    refine ⟨gs2, ws1 ++ [wk], hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by have hmul : c * (k + 1) = c * k + c := by ring
         omega,
      by simp [hwl1],
      fun w hw => by
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have := hext12.length_le; have := hwsW1 w hw; omega
        · exact hwk,
      ?_⟩
    intro i hi
    by_cases hik : i < k
    · have hget : (ws1 ++ [wk]).getD i 0 = ws1.getD i 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < ws1.length)]
      rw [hget]
      have hmem : ws1.getD i 0 ∈ ws1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      exact hP_mono i (by omega) gs1 gs2 _ (hwsW1 _ hmem) hext12 (hP1 i hik)
    · have hieq : i = k := by omega
      rw [hieq]
      have hget : (ws1 ++ [wk]).getD k 0 = wk := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : ws1.length ≤ k)]
        simp [hwl1]
      rw [hget]
      exact hPk

lemma exists_sim_D_mono_aux {m : ℕ} (wF wT : ℕ) (hwF : wF < m) (hwT : wT < m) :
    ∀ (dg : List Gate) (gs : List Gate) (drW : List (ℕ × ℕ)),
      GateOK m gs →
      (∀ g ∈ dg, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) →
      (∀ j < dg.length, ∀ i ∈ (dg.getD j ⟨GateOp.or, []⟩).inputs, i < drW.length + j) →
      (∀ p ∈ drW, p.1 < m + gs.length ∧ p.2 < m + gs.length) →
      ∃ (gs' : List Gate) (drW' : List (ℕ × ℕ)),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + 2 * dg.length ∧
        drW'.length = drW.length + dg.length ∧
        (∀ p ∈ drW', p.1 < m + gs'.length ∧ p.2 < m + gs'.length) ∧
        ∀ (inpC wD : List Bool), inpC.length = m → inpC.getD wF false = false → inpC.getD wT false = true →
          wD.length = drW.length →
          (∀ i < drW.length,
            wVal gs inpC (drW.getD i (0, 0)).1 = wD.getD i false ∧
            wVal gs inpC (drW.getD i (0, 0)).2 = !(wD.getD i false)) →
          ∀ i < drW'.length,
            wVal gs' inpC (drW'.getD i (0, 0)).1 = (evalWires dg wD).getD i false ∧
            wVal gs' inpC (drW'.getD i (0, 0)).2 = !((evalWires dg wD).getD i false) := by
  intro dg
  induction dg with
  | nil =>
    intro gs drW hgs _ _ hdrW
    exact ⟨gs, drW, Extends.refl gs, hgs, rfl, by simp, by simp, hdrW,
      fun inpC wD _ _ _ _ hagree i hi => hagree i (by simpa using hi)⟩
  | cons g dg' ih =>
    intro gs drW hgs hdg1 hdg2 hdrW
    have hg1 := hdg1 g (by simp)
    have hgin : ∀ i ∈ g.inputs, i < drW.length := by
      have h0 := hdg2 0 (by simp)
      simpa [List.getD_eq_getElem?_getD] using h0

    have hstep : ∃ (gs1 : List Gate) (uv : ℕ × ℕ),
        Extends gs gs1 ∧ GateOK m gs1 ∧ notCnt gs1 = notCnt gs ∧
        gs1.length ≤ gs.length + 2 ∧ uv.1 < m + gs1.length ∧ uv.2 < m + gs1.length ∧
        ∀ (inpC wD : List Bool), inpC.length = m → inpC.getD wF false = false → inpC.getD wT false = true →
          wD.length = drW.length →
          (∀ i < drW.length,
            wVal gs inpC (drW.getD i (0, 0)).1 = wD.getD i false ∧
            wVal gs inpC (drW.getD i (0, 0)).2 = !(wD.getD i false)) →
          wVal gs1 inpC uv.1 = g.op.eval (g.inputs.map fun i => wD.getD i false) ∧
          wVal gs1 inpC uv.2 = !(g.op.eval (g.inputs.map fun i => wD.getD i false)) := by
      rcases g with ⟨op, ins⟩
      dsimp only at hg1 hgin
      have hlen2 : ins.length ≤ 2 := hg1.2
      have hpair_lt : ∀ i ∈ ins, (drW.getD i (0, 0)).1 < m + gs.length ∧ (drW.getD i (0, 0)).2 < m + gs.length := by
        intro i hi
        have hilt := hgin i hi
        have hmem : drW.getD i (0, 0) ∈ drW := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hilt]; exact List.getElem_mem _
        exact hdrW _ hmem
      rcases hg1.1 with rfl | rfl | rfl
      ·
        match ins, hlen2, hgin, hpair_lt with
        | [], _, _, _ =>
          refine ⟨gs, (wT, wF), Extends.refl gs, hgs, rfl, by omega, by omega, by omega, ?_⟩
          intro inpC wD hinp hF hT _ _
          rw [evalWires_input gs inpC (by omega), evalWires_input gs inpC (by omega), hF, hT]
          simp [GateOp.eval]
        | [a], _, hgin', hplt =>
          have ha := hgin' a (by simp)
          have hpa := hplt a (by simp)
          refine ⟨gs, drW.getD a (0, 0), Extends.refl gs, hgs, rfl, by omega, hpa.1, hpa.2, ?_⟩
          intro inpC wD _ _ _ _ hag
          simpa [GateOp.eval] using hag a ha
        | [a, b], _, hgin', hplt =>
          have ha := hgin' a (by simp); have hb := hgin' b (by simp)
          have hpa := hplt a (by simp); have hpb := hplt b (by simp)
          let pa := drW.getD a (0, 0); let pb := drW.getD b (0, 0)
          obtain ⟨hgA, hnA, hlA, hu, heA⟩ := mkAnd_step hgs hpa.1 hpb.1
          let gsA := gs ++ [⟨GateOp.and, [pa.1, pb.1]⟩]
          let u := m + gs.length
          have hgsAl : gsA.length = gs.length + 1 := hlA
          obtain ⟨hgB, hnB, hlB, hv, heB⟩ := mkOr_step hgA (by dsimp only [pa]; omega : pa.2 < m + gsA.length) (by dsimp only [pb]; omega : pb.2 < m + gsA.length)
          let gsB := gsA ++ [⟨GateOp.or, [pa.2, pb.2]⟩]
          let v := m + gsA.length
          refine ⟨gsB, (u, v), Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩, hgB, hnB.trans hnA,
            by simp [gsB, gsA], by dsimp only [u]; simp [gsB, gsA], hv, ?_⟩
          intro inpC wD hinp _ _ _ hag
          have eA := heA inpC hinp; have eB := heB inpC hinp
          have haga := hag a ha; have hagb := hag b hb
          constructor
          · rw [eB.1 u (by dsimp only [u]; omega), eA.2, haga.1, hagb.1]; simp [GateOp.eval]
          · rw [eB.2, eA.1 pa.2 hpa.2, eA.1 pb.2 hpb.2, haga.2, hagb.2]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq, Bool.and_true]
            cases wD.getD a false <;> cases wD.getD b false <;> rfl
        | _ :: _ :: _ :: _, hlen2', _, _ => simp at hlen2'
      ·
        match ins, hlen2, hgin, hpair_lt with
        | [], _, _, _ =>
          refine ⟨gs, (wF, wT), Extends.refl gs, hgs, rfl, by omega, by omega, by omega, ?_⟩
          intro inpC wD hinp hF hT _ _
          rw [evalWires_input gs inpC (by omega), evalWires_input gs inpC (by omega), hF, hT]
          simp [GateOp.eval]
        | [a], _, hgin', hplt =>
          have ha := hgin' a (by simp)
          have hpa := hplt a (by simp)
          refine ⟨gs, drW.getD a (0, 0), Extends.refl gs, hgs, rfl, by omega, hpa.1, hpa.2, ?_⟩
          intro inpC wD _ _ _ _ hag
          simpa [GateOp.eval] using hag a ha
        | [a, b], _, hgin', hplt =>
          have ha := hgin' a (by simp); have hb := hgin' b (by simp)
          have hpa := hplt a (by simp); have hpb := hplt b (by simp)
          let pa := drW.getD a (0, 0); let pb := drW.getD b (0, 0)
          obtain ⟨hgA, hnA, hlA, hu, heA⟩ := mkOr_step hgs hpa.1 hpb.1
          let gsA := gs ++ [⟨GateOp.or, [pa.1, pb.1]⟩]
          let u := m + gs.length
          have hgsAl : gsA.length = gs.length + 1 := hlA
          obtain ⟨hgB, hnB, hlB, hv, heB⟩ := mkAnd_step hgA (by dsimp only [pa]; omega : pa.2 < m + gsA.length) (by dsimp only [pb]; omega : pb.2 < m + gsA.length)
          let gsB := gsA ++ [⟨GateOp.and, [pa.2, pb.2]⟩]
          let v := m + gsA.length
          refine ⟨gsB, (u, v), Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩, hgB, hnB.trans hnA,
            by simp [gsB, gsA], by dsimp only [u]; simp [gsB, gsA], hv, ?_⟩
          intro inpC wD hinp _ _ _ hag
          have eA := heA inpC hinp; have eB := heB inpC hinp
          have haga := hag a ha; have hagb := hag b hb
          constructor
          · rw [eB.1 u (by dsimp only [u]; omega), eA.2, haga.1, hagb.1]; simp [GateOp.eval]
          · rw [eB.2, eA.1 pa.2 hpa.2, eA.1 pb.2 hpb.2, haga.2, hagb.2]
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
            cases wD.getD a false <;> cases wD.getD b false <;> rfl
        | _ :: _ :: _ :: _, hlen2', _, _ => simp at hlen2'
      ·
        match ins, hlen2, hgin, hpair_lt with
        | [], _, _, _ =>
          refine ⟨gs, (wT, wF), Extends.refl gs, hgs, rfl, by omega, by omega, by omega, ?_⟩
          intro inpC wD hinp hF hT _ _
          rw [evalWires_input gs inpC (by omega), evalWires_input gs inpC (by omega), hF, hT]
          simp [GateOp.eval]
        | a :: _, _, hgin', hplt =>
          have ha := hgin' a (by simp)
          have hpa := hplt a (by simp)
          let pa := drW.getD a (0, 0)
          refine ⟨gs, (pa.2, pa.1), Extends.refl gs, hgs, rfl, by omega, hpa.2, hpa.1, ?_⟩
          intro inpC wD _ _ _ _ hag
          have haga := hag a ha
          dsimp only [pa]
          rw [haga.1, haga.2]
          simp [GateOp.eval]
    obtain ⟨gs1, uv, hext01, hgs1, hnc1, hlen1, huv1, huv2, hev1⟩ := hstep
    obtain ⟨gs2, drW2, hext12, hgs2, hnc2, hlen2, hdrl2, hdrW2, hev2⟩ :=
      ih gs1 (drW ++ [uv]) hgs1
        (fun g' hg' => hdg1 g' (by simp [hg']))
        (fun j hj i hi => by
          have h := hdg2 (j + 1) (by simp; omega) i (by simpa [List.getD_eq_getElem?_getD] using hi)
          simp only [List.length_append, List.length_singleton]; omega)
        (fun p hp => by
          simp only [List.mem_append, List.mem_singleton] at hp
          rcases hp with hp | rfl
          · have := hext01.length_le; have := hdrW p hp; omega
          · exact ⟨huv1, huv2⟩)
    refine ⟨gs2, drW2, hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by simp only [List.length_cons]; omega,
      by simp only [List.length_append, List.length_singleton] at hdrl2
         simp only [List.length_cons]; omega,
      hdrW2, ?_⟩
    intro inpC wD hinp hF hT hwDl hag i hi
    simp only [evalWires, List.foldl_cons]
    have hstep_ev := hev1 inpC wD hinp hF hT hwDl hag
    have hag1 : ∀ k < (drW ++ [uv]).length,
        wVal gs1 inpC ((drW ++ [uv]).getD k (0, 0)).1 = (wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]).getD k false ∧
        wVal gs1 inpC ((drW ++ [uv]).getD k (0, 0)).2 = !((wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]).getD k false) := by
      intro k hk
      simp only [List.length_append, List.length_singleton] at hk
      by_cases hlt : k < drW.length
      · have h1 : (drW ++ [uv]).getD k (0, 0) = drW.getD k (0, 0) := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hlt]
        have h2 : (wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]).getD k false = wD.getD k false := by
          simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : k < wD.length)]
        rw [h1, h2]
        have hmem : drW.getD k (0, 0) ∈ drW := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]; exact List.getElem_mem _
        have hpk := hdrW _ hmem
        rw [hext01.wVal_eq inpC (by omega), hext01.wVal_eq inpC (by omega)]
        exact hag k hlt
      · have hkeq : k = drW.length := by omega
        subst hkeq
        have h1 : (drW ++ [uv]).getD drW.length (0, 0) = uv := by
          simp [List.getD_eq_getElem?_getD]
        have h2 : (wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]).getD drW.length false =
            g.op.eval (g.inputs.map fun j => wD.getD j false) := by
          simp [List.getD_eq_getElem?_getD, hwDl]
        rw [h1, h2]
        exact hstep_ev
    exact hev2 inpC (wD ++ [g.op.eval (g.inputs.map fun j => wD.getD j false)]) hinp hF hT
      (by simp [hwDl]) hag1 i hi

lemma exists_b_decoder_aux {m : ℕ} (b : ℕ) (wF wT : ℕ) (hwF : wF < m) (hwT : wT < m)
    (T : List ℕ) (hTl : T.length = 2 ^ b) :
    ∀ (d : ℕ) (_hd : d ≤ b) (gs : List Gate), GateOK m gs →
      (∀ w ∈ T, w < m + gs.length) →
      ∃ (gs' : List Gate) (eqP : List ℕ),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs + d ∧
        gs'.length ≤ gs.length + 5 * 2 ^ d ∧ eqP.length = 2 ^ d ∧
        (∀ w ∈ eqP, w < m + gs'.length) ∧
        ∀ (inp : List Bool) (v : ℕ), inp.length = m →
          inp.getD wF false = false → inp.getD wT false = true →
          v < 2 ^ b →
          (∀ k, 1 ≤ k → k < 2 ^ b → wVal gs inp (T.getD k 0) = decide (k ≤ v)) →
          ∀ u < 2 ^ d, wVal gs' inp (eqP.getD u 0) = decide (v / 2 ^ (b - d) = u) := by
  intro d
  induction d with
  | zero =>
    intro _ gs hgs _
    refine ⟨gs, [wT], Extends.refl gs, hgs, by simp, by simp, by simp,
      fun w hw => by simp at hw; subst hw; omega, ?_⟩
    intro inp v hinp _ hT hv _ u hu
    have hu0 : u = 0 := by omega
    subst hu0
    have hdiv : v / 2 ^ b = 0 := Nat.div_eq_of_lt hv
    simp only [Nat.sub_zero, hdiv, decide_true, List.getD_eq_getElem?_getD,
      List.getElem?_cons_zero, Option.getD_some]
    rw [evalWires_input gs inp (by omega), hT]
  | succ d ih =>
    intro hdb gs hgs hTW
    obtain ⟨gs1, eqP, hext01, hgs1, hnc1, hlen1, heqPl, heqPW, hev1⟩ :=
      ih (by omega) gs hgs hTW
    let p := b - (d + 1)
    have hbd : b - d = p + 1 := by dsimp only [p]; omega

    have hbp_build : ∀ (cnt : ℕ) (_hcnt : cnt ≤ 2 ^ d) (gsA : List Gate),
        Extends gs1 gsA → GateOK m gsA →
        ∃ (gsB : List Gate) (acc : ℕ),
          Extends gsA gsB ∧ GateOK m gsB ∧ notCnt gsB = notCnt gsA ∧
          gsB.length ≤ gsA.length + 2 * cnt ∧ acc < m + gsB.length ∧
          ∀ (inp : List Bool), inp.length = m → inp.getD wF false = false →
            wVal gsB inp acc = decide (∃ u < cnt,
              wVal gs1 inp (eqP.getD u 0) = true ∧
              wVal gs inp (T.getD (u * 2 ^ (p + 1) + 2 ^ p) 0) = true) := by
      intro cnt
      induction cnt with
      | zero =>
        intro _ gsA _ hgsA
        refine ⟨gsA, wF, Extends.refl gsA, hgsA, rfl, by simp, by omega, ?_⟩
        intro inp hinp hF
        rw [evalWires_input gsA inp (by omega), hF]
        simp
      | succ c ihc =>
        intro hc gsA hext1A hgsA
        obtain ⟨gsB, acc, hextAB, hgsB, hncB, hlenB, haccW, hevB⟩ := ihc (by omega) gsA hext1A hgsA
        have hext1B : Extends gs1 gsB := hext1A.trans hextAB
        have hext0B : Extends gs gsB := hext01.trans hext1B
        let eu := eqP.getD c 0
        have heu_mem : eu ∈ eqP := by
          dsimp only [eu]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have heuW : eu < m + gsB.length := by have := hext1B.length_le; have := heqPW _ heu_mem; omega
        have hidx_lt : c * 2 ^ (p + 1) + 2 ^ p < 2 ^ b := by
          have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
          have h2 : c + 1 ≤ 2 ^ d := hc
          have h3 : (c + 1) * 2 ^ (p + 1) ≤ 2 ^ d * 2 ^ (p + 1) := Nat.mul_le_mul_right _ h2
          have h4 : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
          have h5 : 0 < 2 ^ p := Nat.two_pow_pos p
          nlinarith
        let tu := T.getD (c * 2 ^ (p + 1) + 2 ^ p) 0
        have htu_mem : tu ∈ T := by
          dsimp only [tu]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
        have htuW : tu < m + gsB.length := by have := hext0B.length_le; have := hTW _ htu_mem; omega
        obtain ⟨hgC, hnC, hlC, hwC, heC⟩ := mkAnd_step hgsB heuW htuW
        let gsC := gsB ++ [⟨GateOp.and, [eu, tu]⟩]
        let wC := m + gsB.length
        have hgsCl : gsC.length = gsB.length + 1 := hlC
        obtain ⟨hgD, hnD, hlD, hwD, heD⟩ := mkOr_step hgC (by omega : acc < m + gsC.length) hwC
        let gsD := gsC ++ [⟨GateOp.or, [acc, wC]⟩]
        let wD := m + gsC.length
        refine ⟨gsD, wD, hextAB.trans (Extends.trans ⟨_, rfl⟩ ⟨_, rfl⟩), hgD,
          hnD.trans (hnC.trans hncB), by simp only [gsD, gsC, List.length_append, List.length_singleton]; omega, hwD, ?_⟩
        intro inp hinp hF
        have eC := heC inp hinp; have eD := heD inp hinp
        rw [eD.2, eC.1 acc haccW, eC.2, hevB inp hinp hF,
          hext1B.wVal_eq inp (by have := heqPW _ heu_mem; omega),
          hext0B.wVal_eq inp (by have := hTW _ htu_mem; omega)]
        apply Bool.eq_iff_iff.2
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
        constructor
        · rintro (⟨u, hu, h1, h2⟩ | ⟨h1, h2⟩)
          · exact ⟨u, by omega, h1, h2⟩
          · exact ⟨c, by omega, h1, h2⟩
        · rintro ⟨u, hu, h1, h2⟩
          by_cases huc : u < c
          · exact Or.inl ⟨u, huc, h1, h2⟩
          · have : u = c := by omega
            subst this; exact Or.inr ⟨h1, h2⟩
    obtain ⟨gs2, bp, hext12, hgs2, hnc2, hlen2, hbpW, hev_bp⟩ := hbp_build (2 ^ d) le_rfl gs1 (Extends.refl gs1) hgs1

    obtain ⟨hgs3, hnc3, hlen3, hnbpW, hev3⟩ := mkNot_step hgs2 hbpW
    let gs3 := gs2 ++ [⟨GateOp.not, [bp]⟩]
    let nbp := m + gs2.length
    have hext23 : Extends gs2 gs3 := ⟨_, rfl⟩
    have hext13 : Extends gs1 gs3 := hext12.trans hext23
    have hgs3l : gs3.length = gs2.length + 1 := hlen3

    have hbp3 : bp < m + gs3.length := by omega
    obtain ⟨gs4, nextP, hext34, hgs4, hnc4, hlen4, hnextl, hnextW, hnextP⟩ :=
      exists_map_build (m := m) 1 (2 ^ (d + 1)) gs3
        (fun u gsX w => ∀ (inp : List Bool), inp.length = m →
          wVal gsX inp w = (wVal gs1 inp (eqP.getD (u / 2) 0) &&
            if u % 2 = 0 then wVal gs3 inp nbp else wVal gs3 inp bp))
        (fun u _ gsA gsB w hw hext hP inp hinp => by rw [hext.wVal_eq inp (by omega)]; exact hP inp hinp)
        (fun u hu gsA hext3A hgsA => by
          have hud : u / 2 < 2 ^ d := by
            have h2d : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
            omega
          let eu := eqP.getD (u / 2) 0
          have heu_mem : eu ∈ eqP := by
            dsimp only [eu]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
          have hext1A : Extends gs1 gsA := hext13.trans hext3A
          have heuA : eu < m + gsA.length := by have := hext1A.length_le; have := heqPW _ heu_mem; omega
          let bitW := if u % 2 = 0 then nbp else bp
          have hbitA : bitW < m + gsA.length := by
            have := hext3A.length_le; dsimp only [bitW]; split_ifs <;> omega
          obtain ⟨hgB, hnB, hlB, hwB, heB⟩ := mkAnd_step hgsA heuA hbitA
          refine ⟨gsA ++ [⟨GateOp.and, [eu, bitW]⟩], m + gsA.length, ⟨_, rfl⟩, hgB, hnB, by omega, hwB, ?_⟩
          intro inp hinp
          rw [(heB inp hinp).2, hext1A.wVal_eq inp (by have := heqPW _ heu_mem; omega)]
          congr 1
          dsimp only [bitW]
          split_ifs
          · exact hext3A.wVal_eq inp (by omega)
          · exact hext3A.wVal_eq inp (by omega))
        hgs3
    have hpow : 2 ^ (d + 1) = 2 * 2 ^ d := by ring
    have hpos : 1 ≤ 2 ^ d := Nat.one_le_two_pow
    have hlen_tot : gs4.length ≤ gs.length + 5 * 2 ^ (d + 1) := by omega
    have hnc_tot : notCnt gs4 = notCnt gs + (d + 1) := by rw [hnc4, hnc3, hnc2, hnc1]; omega
    refine ⟨gs4, nextP, hext01.trans (hext13.trans hext34), hgs4, hnc_tot, hlen_tot, hnextl, hnextW, ?_⟩
    intro inp v hinp hF hT hv hTspec u hu
    rw [hnextP u hu inp hinp]
    have hud : u / 2 < 2 ^ d := by omega
    have heq_u2 : wVal gs1 inp (eqP.getD (u / 2) 0) = decide (v / 2 ^ (p + 1) = u / 2) := by
      rw [hev1 inp v hinp hF hT hv hTspec (u / 2) hud, hbd]
    have hbp_val : wVal gs2 inp bp = decide ((v / 2 ^ p) % 2 = 1) := by
      rw [hev_bp inp hinp hF]
      apply Bool.eq_iff_iff.2
      simp only [decide_eq_true_eq]
      have hdiv2 : v / 2 ^ (p + 1) = (v / 2 ^ p) / 2 := by
        rw [pow_succ, Nat.div_div_eq_div_mul]
      have hvp_lt : v / 2 ^ (p + 1) < 2 ^ d := by
        have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)]
        omega
      have hidx_pos : 1 ≤ (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p := by
        have := Nat.two_pow_pos p; omega
      have hidx_lt : (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p < 2 ^ b := by
        have h1 : 2 ^ b = 2 ^ d * 2 ^ (p + 1) := by rw [← pow_add]; congr 1; dsimp only [p]; omega
        have h2 : (v / 2 ^ (p + 1) + 1) * 2 ^ (p + 1) ≤ 2 ^ d * 2 ^ (p + 1) :=
          Nat.mul_le_mul_right _ (by omega)
        have h3 : 2 ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
        have h4 := Nat.two_pow_pos p
        nlinarith
      have hiff_arith : (v / 2 ^ (p + 1)) * 2 ^ (p + 1) + 2 ^ p ≤ v ↔ (v / 2 ^ p) % 2 = 1 := by
        have hm := Nat.div_add_mod v (2 ^ p)
        have hmlt := Nat.mod_lt v (Nat.two_pow_pos p)
        have hm2 := Nat.div_add_mod (v / 2 ^ p) 2
        have hm2lt : (v / 2 ^ p) % 2 < 2 := Nat.mod_lt _ (by omega)
        have hp2 : 2 ^ (p + 1) = 2 * 2 ^ p := by ring
        rw [hdiv2, hp2]
        generalize 2 ^ p = P at hm hmlt ⊢
        generalize v / P = A at hm hm2 hm2lt ⊢
        have hA2 : A % 2 = 0 ∨ A % 2 = 1 := by omega
        rcases hA2 with h0 | h1
        · have hAeq : A = 2 * (A / 2) := by omega
          have hmul : A / 2 * (2 * P) = P * A := by (conv_rhs => rw [hAeq]); ring
          rw [h0, hmul]
          constructor
          · intro h; omega
          · intro h; omega
        · have hAeq : A = 2 * (A / 2) + 1 := by omega
          have hmul : A / 2 * (2 * P) + P = P * A := by (conv_rhs => rw [hAeq]); ring
          rw [h1, hmul]
          constructor
          · intro _; rfl
          · intro _; omega
      constructor
      · rintro ⟨w, hw, hw1, hw2⟩
        rw [hev1 inp v hinp hF hT hv hTspec w hw, hbd, decide_eq_true_eq] at hw1
        subst hw1
        rw [hTspec _ hidx_pos hidx_lt, decide_eq_true_eq] at hw2
        exact hiff_arith.1 hw2
      · intro hmod
        refine ⟨v / 2 ^ (p + 1), hvp_lt, ?_, ?_⟩
        · rw [hev1 inp v hinp hF hT hv hTspec _ hvp_lt, hbd]; simp
        · rw [hTspec _ hidx_pos hidx_lt, decide_eq_true_eq]
          exact hiff_arith.2 hmod
    have hbp3_val : wVal gs3 inp bp = decide ((v / 2 ^ p) % 2 = 1) := by
      rw [(hev3 inp hinp).1 bp hbpW, hbp_val]
    have hnbp3_val : wVal gs3 inp nbp = decide ((v / 2 ^ p) % 2 = 0) := by
      rw [(hev3 inp hinp).2, hbp_val]
      have hmod2 : (v / 2 ^ p) % 2 = 0 ∨ (v / 2 ^ p) % 2 = 1 := by omega
      rcases hmod2 with h | h <;> simp [h]
    have hdiv2 : v / 2 ^ (p + 1) = (v / 2 ^ p) / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    rw [heq_u2, hbp3_val, hnbp3_val, hdiv2]
    split_ifs with hpar
    · apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      dsimp only [p]; omega
    · apply Bool.eq_iff_iff.2
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      dsimp only [p]; omega

lemma exists_prefix_or {m : ℕ} (ws : List ℕ) :
    ∀ (k : ℕ) (_hk : k < ws.length) (gs : List Gate), GateOK m gs →
      (∀ w ∈ ws, w < m + gs.length) →
      ∃ (gs' : List Gate) (leW : List ℕ),
        Extends gs gs' ∧ GateOK m gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + k ∧ leW.length = k + 1 ∧
        (∀ w ∈ leW, w < m + gs'.length) ∧
        ∀ inp : List Bool, inp.length = m →
          ∀ j ≤ k, wVal gs' inp (leW.getD j 0) = decide (∃ i ≤ j, wVal gs inp (ws.getD i 0) = true) := by
  intro k
  induction k with
  | zero =>
    intro hk gs hgs hwsW
    have hw0_mem : ws.getD 0 0 ∈ ws := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
    refine ⟨gs, [ws.getD 0 0], Extends.refl gs, hgs, rfl, by simp, rfl,
      fun w hw => by simp at hw; subst hw; exact hwsW _ hw0_mem, ?_⟩
    intro inp _ j hj
    have hj0 : j = 0 := by omega
    subst hj0
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons_zero, Option.getD_some,
      Nat.le_zero, exists_eq_left]
    cases wVal gs inp (ws.getD 0 0) <;> rfl
  | succ k ih =>
    intro hk gs hgs hwsW
    obtain ⟨gs1, leW1, hext01, hgs1, hnc1, hlen1, hl1, hW1, hev1⟩ := ih (by omega) gs hgs hwsW
    let prev := leW1.getD k 0
    have hprev_mem : prev ∈ leW1 := by
      dsimp only [prev]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
    let cur := ws.getD (k + 1) 0
    have hcur_mem : cur ∈ ws := by
      dsimp only [cur]; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]; exact List.getElem_mem _
    have hcur1 : cur < m + gs1.length := by have := hext01.length_le; have := hwsW _ hcur_mem; omega
    obtain ⟨hgs2, hnc2, hlen2, hw2, hev2⟩ := mkOr_step hgs1 (hW1 _ hprev_mem) hcur1
    let gs2 := gs1 ++ [⟨GateOp.or, [prev, cur]⟩]
    let w2 := m + gs1.length
    have hext12 : Extends gs1 gs2 := ⟨_, rfl⟩
    refine ⟨gs2, leW1 ++ [w2], hext01.trans hext12, hgs2, hnc2.trans hnc1,
      by simp only [gs2, List.length_append, List.length_singleton]; omega,
      by simp [hl1],
      fun w hw => by
        simp only [List.mem_append, List.mem_singleton] at hw
        rcases hw with hw | rfl
        · have := hext12.length_le; have := hW1 w hw; omega
        · exact hw2,
      ?_⟩
    intro inp hinp j hj
    by_cases hjk : j ≤ k
    · have hget : (leW1 ++ [w2]).getD j 0 = leW1.getD j 0 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : j < leW1.length)]
      rw [hget]
      have hmem : leW1.getD j 0 ∈ leW1 := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      rw [hext12.wVal_eq inp (by have := hW1 _ hmem; omega)]
      exact hev1 inp hinp j hjk
    · have hjeq : j = k + 1 := by omega
      subst hjeq
      have hget : (leW1 ++ [w2]).getD (k + 1) 0 = w2 := by
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : leW1.length ≤ k + 1)]
        simp [hl1]
      rw [hget, (hev2 inp hinp).2, hev1 inp hinp k le_rfl,
        hext01.wVal_eq inp (by have := hwsW _ hcur_mem; omega)]
      apply Bool.eq_iff_iff.2
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨i, hi, hv⟩ | hv)
        · exact ⟨i, by omega, hv⟩
        · exact ⟨k + 1, le_rfl, hv⟩
      · rintro ⟨i, hi, hv⟩
        by_cases hik : i ≤ k
        · exact Or.inl ⟨i, hik, hv⟩
        · have : i = k + 1 := by omega
          subst this; exact Or.inr hv

lemma count_true_ofFn_mem {q : ℕ} (z : Finset (Fin q)) :
    (List.ofFn fun t : Fin q => decide (t ∈ z)).count true = z.card := by
  rw [count_true_ofFn_eq]
  have h1 : (∑ t : Fin q, if decide (t ∈ z) = true then 1 else 0) =
      ∑ t : Fin q, if t ∈ z then 1 else 0 := by
    apply Finset.sum_congr rfl; intro t _; simp
  rw [h1, ← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
  simp

def notInBit (w : List Bool) (g : Gate) : ℕ :=
  if (g.inputs.map fun i => w.getD i false).headD false then 1 else 0

def notCodeFrom (w : List Bool) : List Gate → ℕ
  | [] => 0
  | g :: gs =>
      let w' := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
      if isNotOp g.op then
        notInBit w g * 2 ^ notCnt gs + notCodeFrom w' gs
      else
        notCodeFrom w' gs

lemma notCnt_cons (g : Gate) (gs : List Gate) :
    notCnt (g :: gs) = (if isNotOp g.op then 1 else 0) + notCnt gs := by
  unfold notCnt
  rw [List.filter_cons]
  cases isNotOp g.op <;> simp [Nat.add_comm]

lemma notCodeFrom_lt (gs : List Gate) (w : List Bool) :
    notCodeFrom w gs < 2 ^ notCnt gs := by
  induction gs generalizing w with
  | nil => simp [notCodeFrom, notCnt]
  | cons g gs ih =>
    simp only [notCodeFrom, notCnt_cons]
    split_ifs with hnot
    · have hih := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      have hbit : notInBit w g ≤ 1 := by unfold notInBit; split_ifs <;> omega
      have hpow : 2 ^ (1 + notCnt gs) = 2 ^ notCnt gs + 2 ^ notCnt gs := by
        rw [pow_add, pow_one]; ring
      rw [hpow]
      nlinarith
    · simp only [zero_add]
      exact ih _

lemma notCodeFrom_mono_and_fall (gs : List Gate)
    (hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (w1 w2 : List Bool), w1.length = w2.length →
      (∀ i : ℕ, w1.getD i false = true → w2.getD i false = true) →
      notCodeFrom w1 gs ≤ notCodeFrom w2 gs ∧
      ((∃ i : ℕ, (evalWires gs w1).getD i false = true ∧ (evalWires gs w2).getD i false = false) →
       notCodeFrom w1 gs < notCodeFrom w2 gs) := by
  induction gs with
  | nil =>
    intro w1 w2 _ hle
    refine ⟨le_rfl, ?_⟩
    rintro ⟨i, h1, h2⟩
    simp only [evalWires, List.foldl_nil] at h1 h2
    have := hle i h1
    rw [h2] at this; cases this
  | cons g gs ih =>
    intro w1 w2 hlen hle
    have hg := hop g (by simp)
    have hrest : ∀ g' ∈ gs, g'.op = GateOp.and ∨ g'.op = GateOp.or ∨ g'.op = GateOp.not :=
      fun g' hg' => hop g' (by simp [hg'])
    let v1 := g.op.eval (g.inputs.map fun i => w1.getD i false)
    let v2 := g.op.eval (g.inputs.map fun i => w2.getD i false)
    let w1' := w1 ++ [v1]
    let w2' := w2 ++ [v2]
    have hstep_le : (v1 = true → v2 = true) →
        ∀ i : ℕ, w1'.getD i false = true → w2'.getD i false = true := by
      intro hv i hi
      by_cases hilt : i < w1.length
      · have h1 : w1'.getD i false = w1.getD i false := by
          simp only [w1', List.getD_eq_getElem?_getD, List.getElem?_append_left hilt]
        have h2 : w2'.getD i false = w2.getD i false := by
          simp only [w2', List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega : i < w2.length)]
        rw [h1] at hi; rw [h2]; exact hle i hi
      · by_cases hieq : i = w1.length
        · subst hieq
          have h1 : w1'.getD w1.length false = v1 := by simp [w1', List.getD_eq_getElem?_getD]
          have h2 : w2'.getD w1.length false = v2 := by simp [w2', hlen, List.getD_eq_getElem?_getD]
          rw [h1] at hi; rw [h2]; exact hv hi
        · have h1 : w1'.getD i false = false := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [w1']; omega)]; rfl
          rw [h1] at hi; cases hi
    rcases hg with hAnd | hOr | hNot
    · have hnotF : isNotOp g.op = false := by rw [hAnd]; rfl
      have hv : v1 = true → v2 = true := by
        dsimp only [v1, v2]; rw [hAnd]; simp only [GateOp.eval, List.all_eq_true, id_eq]
        intro hall b hb
        rcases List.mem_map.1 hb with ⟨i, hi, rfl⟩
        exact hle i (hall (w1.getD i false) (List.mem_map_of_mem hi))
      have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
      simpa [notCodeFrom, hnotF, evalWires, List.foldl_cons, w1', w2', v1, v2] using hih
    · have hnotF : isNotOp g.op = false := by rw [hOr]; rfl
      have hv : v1 = true → v2 = true := by
        dsimp only [v1, v2]; rw [hOr]; simp only [GateOp.eval, List.any_eq_true, id_eq]
        rintro ⟨b, hb, rfl⟩
        rcases List.mem_map.1 hb with ⟨i, hi, hwi⟩
        exact ⟨w2.getD i false, List.mem_map_of_mem hi, hle i hwi⟩
      have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
      simpa [notCodeFrom, hnotF, evalWires, List.foldl_cons, w1', w2', v1, v2] using hih
    · have hnotT : isNotOp g.op = true := by rw [hNot]; rfl
      let b1 := (g.inputs.map fun i => w1.getD i false).headD false
      let b2 := (g.inputs.map fun i => w2.getD i false).headD false
      have hb_le : b1 = true → b2 = true := by
        dsimp only [b1, b2]
        cases hgin : g.inputs with
        | nil => intro h; simp at h
        | cons a _ => simp only [List.map_cons, List.headD_cons]; exact hle a
      have hv1 : v1 = !b1 := by dsimp only [v1, b1]; rw [hNot]; rfl
      have hv2 : v2 = !b2 := by dsimp only [v2, b2]; rw [hNot]; rfl
      by_cases hbeq : b1 = b2
      · have hbit : notInBit w1 g = notInBit w2 g := by
          unfold notInBit; change (if b1 then 1 else 0) = (if b2 then 1 else 0); rw [hbeq]
        have hv : v1 = true → v2 = true := by rw [hv1, hv2, hbeq]; exact id
        have hih := ih hrest w1' w2' (by simp [w1', w2', hlen]) (hstep_le hv)
        simp only [notCodeFrom, hnotT, ↓reduceIte, evalWires, List.foldl_cons] at hih ⊢
        rw [hbit]
        exact ⟨Nat.add_le_add_left hih.1 _, fun hex => Nat.add_lt_add_left (hih.2 hex) _⟩
      · have hb1F : b1 = false := by
          cases hb1 : b1 with
          | false => rfl
          | true => exact absurd (hb_le hb1).symm (by rw [hb1] at hbeq; exact hbeq)
        have hb2T : b2 = true := by
          cases hb2 : b2 with
          | true => rfl
          | false => exact absurd (hb1F.trans hb2.symm) hbeq
        have hbit1 : notInBit w1 g = 0 := by unfold notInBit; change (if b1 then 1 else 0) = 0; rw [hb1F]; rfl
        have hbit2 : notInBit w2 g = 1 := by unfold notInBit; change (if b2 then 1 else 0) = 1; rw [hb2T]; rfl
        have hlt1 := notCodeFrom_lt gs w1'
        have hstrict : notCodeFrom w1 (g :: gs) < notCodeFrom w2 (g :: gs) := by
          simp only [notCodeFrom, hnotT, ↓reduceIte, hbit1, hbit2, zero_mul, zero_add, one_mul]
          dsimp only [w1', v1] at hlt1
          omega
        exact ⟨le_of_lt hstrict, fun _ => hstrict⟩

lemma inpVec_le_of_subset {n : ℕ} {u v : Finset (Fin n)} (huv : u ⊆ v) :
    (inpVec n u).length = (inpVec n v).length ∧
    ∀ i : ℕ, (inpVec n u).getD i false = true → (inpVec n v).getD i false = true := by
  refine ⟨by rw [inpVec_length, inpVec_length], ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [inpVec_getD_lt n u ⟨i, hin⟩, decide_eq_true_eq] at hi
    rw [inpVec_getD_lt n v ⟨i, hin⟩, decide_eq_true_eq]
    exact huv hi
  · by_cases him : i = n
    · rw [him, inpVec_getD_m n u] at hi; cases hi
    · by_cases him1 : i = n + 1
      · rw [him1]; exact inpVec_getD_m1 n v
      · have hnone : (inpVec n u).getD i false = false := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [inpVec_length]; omega)]; rfl
        rw [hnone] at hi; cases hi

lemma markov_chain_bound {n : ℕ} (gs : List Gate) (hgs : GateOK (n + 2) gs)
    (M : ℕ) (S : ℕ → Finset (Fin n))
    (hsub : ∀ t < M, S t ⊆ S (t + 1))
    (hfall : ∀ t < M, ∃ w : ℕ, wVal gs (inpVec n (S t)) w = true ∧ wVal gs (inpVec n (S (t + 1))) w = false) :
    M < 2 ^ notCnt gs := by
  have hop : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hgs.1 g hg).1
  have hle : ∀ k ≤ M, k ≤ notCodeFrom (inpVec n (S k)) gs := by
    intro k
    induction k with
    | zero => intro _; exact Nat.zero_le _
    | succ k ih =>
      intro hk
      have hih := ih (by omega)
      have hvec := inpVec_le_of_subset (hsub k (by omega))
      have hlt := (notCodeFrom_mono_and_fall gs hop _ _ hvec.1 hvec.2).2 (hfall k (by omega))
      omega
  have hM := hle M le_rfl
  have hlt := notCodeFrom_lt gs (inpVec n (S M))
  omega

lemma exists_subset_chain {α : Type*} [DecidableEq α] (B : Finset α) :
    ∃ (A : ℕ → Finset α),
      A 0 = ∅ ∧ A B.card = B ∧
      ∀ t < B.card, ∃ a : α, A (t + 1) = insert a (A t) ∧ a ∉ A t ∧ (A t).card = t := by
  induction B using Finset.induction_on with
  | empty =>
    exact ⟨fun _ => ∅, rfl, rfl, fun t ht => by simp at ht⟩
  | insert x s hx ih =>
    rcases ih with ⟨A, h0, hcard, hstep⟩
    let A' : ℕ → Finset α := fun t => if t ≤ s.card then A t else insert x s
    refine ⟨A', by simp [A', h0], by simp [A', Finset.card_insert_of_notMem hx], ?_⟩
    intro t ht
    rw [Finset.card_insert_of_notMem hx] at ht
    by_cases hts : t < s.card
    · rcases hstep t hts with ⟨a, ha1, ha2, ha3⟩
      refine ⟨a, ?_, ?_, ?_⟩
      · simp only [A', show t + 1 ≤ s.card by omega, show t ≤ s.card by omega, ↓reduceIte]; exact ha1
      · simp only [A', show t ≤ s.card by omega, ↓reduceIte]; exact ha2
      · simp only [A', show t ≤ s.card by omega, ↓reduceIte]; exact ha3
    · have hteq : t = s.card := by omega
      subst hteq
      refine ⟨x, ?_, ?_, ?_⟩
      · simp [A', hcard]
      · simp [A', hcard, hx]
      · simp [A', hcard]

def remapIdx (mC : ℕ) (phi : ℕ → ℕ) (base : ℕ) (i : ℕ) : ℕ :=
  if i < mC then phi i else base + (i - mC)

def remapGates (mC : ℕ) (phi : ℕ → ℕ) (base : ℕ) (cg : List Gate) : List Gate :=
  cg.map fun g => ⟨g.op, g.inputs.map (remapIdx mC phi base)⟩

lemma GateOK_remap {mD mC : ℕ} {pre cg : List Gate} (hpre : GateOK mD pre) (hcg : GateOK mC cg)
    (phi : ℕ → ℕ) (hphi : ∀ i < mC, phi i < mD + pre.length) :
    GateOK mD (pre ++ remapGates mC phi (mD + pre.length) cg) := by
  refine ⟨?_, ?_⟩
  · intro g hg
    simp only [List.mem_append, remapGates, List.mem_map] at hg
    rcases hg with hg | ⟨g0, hg0, rfl⟩
    · exact hpre.1 g hg
    · have h := hcg.1 g0 hg0
      exact ⟨h.1, by simp [h.2]⟩
  · intro j hj i hi
    simp only [List.length_append, remapGates, List.length_map] at hj
    by_cases hjp : j < pre.length
    · have hget : (pre ++ remapGates mC phi (mD + pre.length) cg).getD j ⟨GateOp.or, []⟩ =
          pre.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [hget] at hi
      exact hpre.2 j hjp i hi
    · have hget : (pre ++ remapGates mC phi (mD + pre.length) cg).getD j ⟨GateOp.or, []⟩ =
          (remapGates mC phi (mD + pre.length) cg).getD (j - pre.length) ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega : pre.length ≤ j)]
      rw [hget] at hi
      have hjk : j - pre.length < cg.length := by omega
      have hget2 : (remapGates mC phi (mD + pre.length) cg).getD (j - pre.length) ⟨GateOp.or, []⟩ =
          ⟨(cg.getD (j - pre.length) ⟨GateOp.or, []⟩).op,
           (cg.getD (j - pre.length) ⟨GateOp.or, []⟩).inputs.map (remapIdx mC phi (mD + pre.length))⟩ := by
        simp only [remapGates, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_getElem (by simp [hjk]), List.getElem?_eq_getElem hjk]
        simp
      rw [hget2] at hi
      rcases List.mem_map.1 hi with ⟨i0, hi0, rfl⟩
      have hi0lt := hcg.2 (j - pre.length) hjk i0 hi0
      unfold remapIdx
      split_ifs with him
      · have := hphi i0 him; omega
      · omega

lemma wVal_remap {mD mC : ℕ} (pre : List Gate) (phi : ℕ → ℕ) (hphi : ∀ i < mC, phi i < mD + pre.length)
    (inpD inpC : List Bool) (hinpD : inpD.length = mD) (hinpC : inpC.length = mC)
    (hmatch : ∀ i < mC, wVal pre inpD (phi i) = inpC.getD i false) :
    ∀ (cg : List Gate), GateOK mC cg →
      ∀ i < mC + cg.length,
        wVal (pre ++ remapGates mC phi (mD + pre.length) cg) inpD (remapIdx mC phi (mD + pre.length) i) =
        wVal cg inpC i := by
  intro cg
  induction cg using List.reverseRecOn with
  | nil =>
    intro _ i hi
    simp only [List.length_nil, add_zero] at hi
    simp only [remapGates, List.map_nil, List.append_nil, remapIdx, hi, ↓reduceIte]
    rw [hmatch i hi, evalWires_input [] inpC (by omega)]
  | append_singleton cg1 g ih =>
    intro hcg i hi
    have hcg1 : GateOK mC cg1 := by
      refine ⟨fun g' hg' => hcg.1 g' (by simp [hg']), fun j hj k hk => ?_⟩
      have h := hcg.2 j (by simp; omega) k
      have hget : (cg1 ++ [g]).getD j ⟨GateOp.or, []⟩ = cg1.getD j ⟨GateOp.or, []⟩ := by
        simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
      rw [hget] at h; exact h hk
    have hgin : ∀ k ∈ g.inputs, k < mC + cg1.length := by
      have h := hcg.2 cg1.length (by simp)
      have hget : (cg1 ++ [g]).getD cg1.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [hget] at h; exact h
    have hrm_app : pre ++ remapGates mC phi (mD + pre.length) (cg1 ++ [g]) =
        (pre ++ remapGates mC phi (mD + pre.length) cg1) ++
        [⟨g.op, g.inputs.map (remapIdx mC phi (mD + pre.length))⟩] := by
      simp [remapGates, List.append_assoc]
    rw [hrm_app]
    simp only [List.length_append, List.length_singleton] at hi
    by_cases hilt : i < mC + cg1.length
    · have hidx_lt : remapIdx mC phi (mD + pre.length) i <
          inpD.length + (pre ++ remapGates mC phi (mD + pre.length) cg1).length := by
        simp only [List.length_append, remapGates, List.length_map, hinpD]
        unfold remapIdx
        split_ifs with him
        · have := hphi i him; omega
        · omega
      rw [evalWires_prefix_getD _ _ inpD hidx_lt, evalWires_prefix_getD cg1 [g] inpC (by omega)]
      exact ih hcg1 i hilt
    · have hieq : i = mC + cg1.length := by omega
      subst hieq
      have hidx_eq : remapIdx mC phi (mD + pre.length) (mC + cg1.length) =
          inpD.length + (pre ++ remapGates mC phi (mD + pre.length) cg1).length := by
        simp only [remapIdx, show ¬ (mC + cg1.length < mC) by omega, ↓reduceIte,
          List.length_append, remapGates, List.length_map, hinpD]
        omega
      have hrhs : wVal (cg1 ++ [g]) inpC (mC + cg1.length) = g.op.eval (g.inputs.map (wVal cg1 inpC)) := by
        rw [← hinpC]; exact wVal_append_gate cg1 g inpC
      rw [hidx_eq, wVal_append_gate, hrhs]
      congr 1
      rw [List.map_map]
      apply List.map_congr_left
      intro k hk
      simp only [Function.comp_apply]
      exact ih hcg1 k (hgin k hk)

lemma notCnt_eq_notCount (C : Circuit) : notCnt C.gates = PEqualNP.NotBracket.notCount C := by
  unfold notCnt PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g _
  cases g.op <;> rfl

def bitsVec (l : ℕ) (x : Finset (Fin l)) : List Bool :=
  List.ofFn fun i : Fin l => decide (i ∈ x)

def pairInp (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) : List Bool :=
  bitsVec n x ++ bitsVec m z ++ [false, true]

lemma bitsVec_length (l : ℕ) (x : Finset (Fin l)) : (bitsVec l x).length = l := by
  simp [bitsVec]

lemma pairInp_length (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairInp n m x z).length = n + m + 2 := by
  simp [pairInp, bitsVec]; omega

lemma pairInp_getD_x (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) (i : Fin n) :
    (pairInp n m x z).getD i.val false = decide (i ∈ x) := by
  simp only [pairInp, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [bitsVec]; omega),
    List.getElem?_append_left (by simp [bitsVec])]
  simp [bitsVec]

lemma pairInp_getD_z (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) (j : Fin m) :
    (pairInp n m x z).getD (n + j.val) false = decide (j ∈ z) := by
  simp only [pairInp, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left (by simp [bitsVec]),
    List.getElem?_append_right (by simp [bitsVec])]
  simp [bitsVec]

lemma pairInp_getD_F (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairInp n m x z).getD (n + m) false = false := by
  simp only [pairInp, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [bitsVec])]
  simp [bitsVec]

lemma pairInp_getD_T (n m : ℕ) (x : Finset (Fin n)) (z : Finset (Fin m)) :
    (pairInp n m x z).getD (n + m + 1) false = true := by
  simp only [pairInp, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp [bitsVec])]
  simp [bitsVec]

lemma pairInp_le_of_subset {n m : ℕ} {x1 x2 : Finset (Fin n)} {z1 z2 : Finset (Fin m)}
    (hx : x1 ⊆ x2) (hz : z1 ⊆ z2) :
    ∀ i : ℕ, (pairInp n m x1 z1).getD i false = true → (pairInp n m x2 z2).getD i false = true := by
  intro i hi
  by_cases h1 : i < n
  · rw [pairInp_getD_x n m x1 z1 ⟨i, h1⟩] at hi
    rw [pairInp_getD_x n m x2 z2 ⟨i, h1⟩, decide_eq_true_eq]
    exact hx (of_decide_eq_true hi)
  · by_cases h2 : i < n + m
    · have hij : i = n + (i - n) := by omega
      rw [hij] at hi ⊢
      rw [pairInp_getD_z n m x1 z1 ⟨i - n, by omega⟩] at hi
      rw [pairInp_getD_z n m x2 z2 ⟨i - n, by omega⟩, decide_eq_true_eq]
      exact hz (of_decide_eq_true hi)
    · by_cases h3 : i = n + m
      · rw [h3, pairInp_getD_F] at hi; cases hi
      · by_cases h4 : i = n + m + 1
        · rw [h4, pairInp_getD_T]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [pairInp_length]; omega)] at hi
          cases hi

def targetVal (k n m : ℕ) (f : Finset (Fin n) → Bool)
    (x : Finset (Fin n)) (z : Finset (Fin m)) : Bool :=
  if z.card < k then decide (z.card % 2 = 0)
  else if z.card = k then !(f x)
  else decide (z.card % 2 = 1)

def preZ (m t : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun j : Fin m => j.val < t

lemma mem_preZ {m t : ℕ} (j : Fin m) : j ∈ preZ m t ↔ j.val < t := by
  simp [preZ]

lemma preZ_subset {m t1 t2 : ℕ} (h : t1 ≤ t2) : preZ m t1 ⊆ preZ m t2 := by
  intro j hj
  rw [mem_preZ] at hj ⊢
  omega

lemma card_preZ {m t : ℕ} (ht : t ≤ m) : (preZ m t).card = t := by
  induction t with
  | zero =>
    have hem : preZ m 0 = ∅ := by ext j; simp [preZ]
    rw [hem]; rfl
  | succ t ih =>
    have heq : preZ m (t + 1) = insert ⟨t, by omega⟩ (preZ m t) := by
      ext j
      simp only [mem_preZ, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnm : (⟨t, by omega⟩ : Fin m) ∉ preZ m t := by
      rw [mem_preZ]; simp
    rw [heq, Finset.card_insert_of_notMem hnm, ih (by omega)]

lemma split_first_not (gs : List Gate) (hpos : 0 < notCnt gs) :
    ∃ (pre : List Gate) (g : Gate) (suf : List Gate),
      gs = pre ++ g :: suf ∧ notCnt pre = 0 ∧ isNotOp g.op = true ∧ notCnt suf + 1 = notCnt gs := by
  induction gs with
  | nil => simp [notCnt] at hpos
  | cons g gs ih =>
    rw [notCnt_cons] at hpos ⊢
    by_cases hn : isNotOp g.op = true
    · refine ⟨[], g, gs, rfl, rfl, hn, ?_⟩
      simp [hn, Nat.add_comm]
    · have hnf : isNotOp g.op = false := by cases h : isNotOp g.op <;> simp_all
      simp only [hnf, Bool.false_eq_true, ↓reduceIte, zero_add] at hpos ⊢
      obtain ⟨pre, g0, suf, heq, h0, hnot, hcnt⟩ := ih hpos
      refine ⟨g :: pre, g0, suf, by simp [heq], ?_, hnot, hcnt⟩
      rw [notCnt_cons]; simp [hnf, h0]

lemma notCodeFrom_append_zero (pre suf : List Gate) (h0 : notCnt pre = 0) (w : List Bool) :
    notCodeFrom w (pre ++ suf) = notCodeFrom (evalWires pre w) suf := by
  induction pre generalizing w with
  | nil => simp [evalWires]
  | cons g pre ih =>
    rw [notCnt_cons] at h0
    have hnf : isNotOp g.op = false := by
      cases h : isNotOp g.op
      · rfl
      · simp [h] at h0
    have h0' : notCnt pre = 0 := by simp [hnf] at h0; exact h0
    simp only [List.cons_append, notCodeFrom, hnf, Bool.false_eq_true, ↓reduceIte, evalWires, List.foldl_cons]
    exact ih h0' _

lemma notCodeFrom_split_first (pre suf : List Gate) (g : Gate)
    (h0 : notCnt pre = 0) (hnot : isNotOp g.op = true) (w : List Bool) :
    notCodeFrom w (pre ++ g :: suf) =
      notInBit (evalWires pre w) g * 2 ^ notCnt suf + notCodeFrom (evalWires (pre ++ [g]) w) suf := by
  rw [notCodeFrom_append_zero pre (g :: suf) h0 w]
  simp only [notCodeFrom, hnot, ↓reduceIte]
  rw [evalWires_append]
  rfl

lemma Monotone2_of_notCnt_zero (gs : List Gate)
    (hfan : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (h0 : notCnt gs = 0) :
    ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  refine ⟨?_, (hfan g hg).2⟩
  rcases (hfan g hg).1 with h | h | h
  · left; exact h
  · right; exact h
  · exfalso
    have hm : g ∈ gs.filter fun g => isNotOp g.op := List.mem_filter.2 ⟨hg, by simp [isNotOp, h]⟩
    have hpos : 0 < (gs.filter fun g => isNotOp g.op).length := List.length_pos_of_mem hm
    unfold notCnt at h0; omega

lemma Monotone2_remap (mC : ℕ) (phi : ℕ → ℕ) (base : ℕ) (cg : List Gate)
    (hm : ∀ g ∈ cg, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ remapGates mC phi base cg, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [remapGates, List.mem_map] at hg
  rcases hg with ⟨g0, hg0, rfl⟩
  exact ⟨(hm g0 hg0).1, by simp [(hm g0 hg0).2]⟩

lemma GateOK_prefix {m : ℕ} {pre suf : List Gate} (h : GateOK m (pre ++ suf)) : GateOK m pre := by
  refine ⟨fun g hg => h.1 g (List.mem_append_left suf hg), fun j hj i hi => ?_⟩
  have hj2 : j < (pre ++ suf).length := by simp; omega
  have hget : (pre ++ suf).getD j ⟨GateOp.or, []⟩ = pre.getD j ⟨GateOp.or, []⟩ := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left hj]
  have := h.2 j hj2 i (by rw [hget]; exact hi)
  exact this

lemma pos_n_of_ne_const {n : ℕ} (f : Finset (Fin n) → Bool)
    (hf0 : f ∅ = false) (hf1 : f Finset.univ = true) : 0 < n := by
  by_contra h0
  have hn0 : n = 0 := by omega
  subst hn0
  have hu : (Finset.univ : Finset (Fin 0)) = ∅ := by ext i; exact Fin.elim0 i
  rw [hu, hf0] at hf1
  cases hf1

lemma L_lib_1280_part1 (a n : ℕ)
    (f : Finset (Fin n) → Bool)
    (hf0 : f ∅ = false) (hf1 : f Finset.univ = true)
    (C : Circuit)
    (hCok : GateOK (n + 2 * (2 * (2 ^ a - 1)) + 2) C.gates)
    (hCout : C.output < n + 2 * (2 * (2 ^ a - 1)) + 2 + C.gates.length)
    (hCeval : ∀ (x : Finset (Fin n)) (z : Finset (Fin (2 * (2 * (2 ^ a - 1))))),
      wVal C.gates (pairInp n (2 * (2 * (2 ^ a - 1))) x z) C.output =
        targetVal (2 * (2 ^ a - 1)) n (2 * (2 * (2 ^ a - 1))) f x z) :
    let b := a + 1
    b ≤ notCnt C.gates ∧
    (∃ D : Circuit,
      GateOK (n + 2) D.gates ∧ D.output < n + 2 + D.gates.length ∧
      (∀ x : Finset (Fin n), wVal D.gates (inpVec n x) D.output = f x) ∧
      D.gates.length ≤ C.gates.length + 1) ∧
    (notCnt C.gates = b →
      ∃ D : Circuit,
        GateOK (n + 2) D.gates ∧ D.output < n + 2 + D.gates.length ∧
        (∀ x : Finset (Fin n), wVal D.gates (inpVec n x) D.output = f x) ∧
        PEqualNP.MetaComplexity.Monotone2 D ∧
        D.gates.length < C.gates.length) := by
  intro b
  let h := 2 ^ a
  let k := 2 * (h - 1)
  let m := 2 * k
  have hh_pos : 1 ≤ h := Nat.one_le_two_pow
  have hk_def : k = 2 * (h - 1) := rfl
  have hm_def : m = 2 * k := rfl
  have h2b : 2 ^ b = 2 * h := by dsimp only [b, h]; rw [pow_succ, Nat.mul_comm]
  have hop : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not :=
    fun g hg => (hCok.1 g hg).1
  let phiC : Finset (Fin n) → Finset (Fin m) → ℕ :=
    fun x z => notCodeFrom (pairInp n m x z) C.gates
  have hmono : ∀ (x1 x2 : Finset (Fin n)) (z1 z2 : Finset (Fin m)),
      x1 ⊆ x2 → z1 ⊆ z2 → phiC x1 z1 ≤ phiC x2 z2 := by
    intro x1 x2 z1 z2 hx hz
    exact (notCodeFrom_mono_and_fall C.gates hop (pairInp n m x1 z1) (pairInp n m x2 z2)
      (by rw [pairInp_length, pairInp_length]) (pairInp_le_of_subset hx hz)).1
  have hfall : ∀ (x1 x2 : Finset (Fin n)) (z1 z2 : Finset (Fin m)),
      x1 ⊆ x2 → z1 ⊆ z2 →
      targetVal k n m f x1 z1 = true → targetVal k n m f x2 z2 = false →
      phiC x1 z1 < phiC x2 z2 := by
    intro x1 x2 z1 z2 hx hz h1 h2
    exact (notCodeFrom_mono_and_fall C.gates hop (pairInp n m x1 z1) (pairInp n m x2 z2)
      (by rw [pairInp_length, pairInp_length]) (pairInp_le_of_subset hx hz)).2
      ⟨C.output, by rw [← hCeval x1 z1] at h1; exact h1, by rw [← hCeval x2 z2] at h2; exact h2⟩

  have hpre_ge : ∀ j ≤ h - 1, j ≤ phiC ∅ (preZ m (2 * j)) := by
    intro j
    induction j with
    | zero => intro _; omega
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hlt : phiC ∅ (preZ m (2 * j)) < phiC ∅ (preZ m (2 * j + 1)) := by
        apply hfall ∅ ∅ (preZ m (2 * j)) (preZ m (2 * j + 1)) (Finset.Subset.refl _)
          (preZ_subset (by omega))
        · unfold targetVal
          rw [card_preZ (by omega : 2 * j ≤ m)]
          simp only [show 2 * j < k by omega, ↓reduceIte, decide_eq_true_eq]; omega
        · unfold targetVal
          rw [card_preZ (by omega : 2 * j + 1 ≤ m)]
          simp only [show 2 * j + 1 < k by omega, ↓reduceIte, decide_eq_false_iff_not]; omega
      have hle2 : phiC ∅ (preZ m (2 * j + 1)) ≤ phiC ∅ (preZ m (2 * (j + 1))) :=
        hmono ∅ ∅ _ _ (Finset.Subset.refl _) (preZ_subset (by omega))
      omega

  have hsuf_ge : ∀ j ≤ h - 1, phiC Finset.univ (preZ m k) + j ≤ phiC Finset.univ (preZ m (k + 2 * j)) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      have h1 := ih (by omega)
      have hle1 : phiC Finset.univ (preZ m (k + 2 * j)) ≤ phiC Finset.univ (preZ m (k + 2 * j + 1)) :=
        hmono _ _ _ _ (Finset.Subset.refl _) (preZ_subset (by omega))
      have hlt : phiC Finset.univ (preZ m (k + 2 * j + 1)) < phiC Finset.univ (preZ m (k + 2 * (j + 1))) := by
        apply hfall Finset.univ Finset.univ _ _ (Finset.Subset.refl _) (preZ_subset (by omega))
        · unfold targetVal
          rw [card_preZ (by omega : k + 2 * j + 1 ≤ m)]
          simp only [show ¬ (k + 2 * j + 1 < k) by omega, show k + 2 * j + 1 ≠ k by omega, ↓reduceIte, decide_eq_true_eq]
          omega
        · unfold targetVal
          rw [card_preZ (by omega : k + 2 * (j + 1) ≤ m)]
          simp only [show ¬ (k + 2 * (j + 1) < k) by omega, show k + 2 * (j + 1) ≠ k by omega, ↓reduceIte, decide_eq_false_iff_not]
          omega
      omega
  have hpre_k : h - 1 ≤ phiC ∅ (preZ m k) := by
    have := hpre_ge (h - 1) le_rfl
    simpa [hk_def] using this
  have hsuf_k : phiC Finset.univ (preZ m k) + (h - 1) < 2 ^ notCnt C.gates := by
    have h1 := hsuf_ge (h - 1) le_rfl
    have h2 := notCodeFrom_lt C.gates (pairInp n m Finset.univ (preZ m (k + 2 * (h - 1))))
    exact Nat.lt_of_le_of_lt h1 h2
  have hmid_fall : phiC ∅ (preZ m k) < phiC Finset.univ (preZ m k) := by
    apply hfall ∅ Finset.univ (preZ m k) (preZ m k) (Finset.empty_subset _) (Finset.Subset.refl _)
    · unfold targetVal; rw [card_preZ (by omega : k ≤ m)]
      simp [hf0]
    · unfold targetVal; rw [card_preZ (by omega : k ≤ m)]
      simp [hf1]

  have hnot_ge : b ≤ notCnt C.gates := by
    have h2le : 2 ^ b ≤ 2 ^ notCnt C.gates := by omega
    by_contra hlt
    have : 2 ^ notCnt C.gates < 2 ^ b := Nat.pow_lt_pow_right (by omega) (by omega)
    omega

  let phiFix : ℕ → ℕ := fun i =>
    if i < n then i
    else if i < n + m then (if i - n < k then n + 1 else n)
    else if i = n + m then n
    else n + 1
  have hphiFix_W : ∀ i < n + m + 2, phiFix i < n + 2 + ([] : List Gate).length := by
    intro i hi; dsimp only [phiFix]
    split_ifs <;> (simp only [List.length_nil, Nat.add_zero]; omega)
  have hphiFix_match : ∀ (x : Finset (Fin n)) (i : ℕ), i < n + m + 2 →
      wVal [] (inpVec n x) (phiFix i) = (pairInp n m x (preZ m k)).getD i false := by
    intro x i hi
    dsimp only [phiFix]
    split_ifs with h1 h2 h3 h4
    · rw [evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega),
        inpVec_getD_lt n x ⟨i, h1⟩, pairInp_getD_x n m x (preZ m k) ⟨i, h1⟩]
    · rw [evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m1 n x]
      have hij : i = n + (i - n) := by omega
      rw [hij, pairInp_getD_z n m x (preZ m k) ⟨i - n, by omega⟩]
      symm; rw [decide_eq_true_eq, mem_preZ]; dsimp only; omega
    · rw [evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m n x]
      have hij : i = n + (i - n) := by omega
      rw [hij, pairInp_getD_z n m x (preZ m k) ⟨i - n, by omega⟩]
      symm; rw [decide_eq_false_iff_not, mem_preZ]; dsimp only; omega
    · rw [evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m n x,
        h4, pairInp_getD_F]
    · have h5 : i = n + m + 1 := by omega
      rw [evalWires_input [] (inpVec n x) (by rw [inpVec_length]; omega), inpVec_getD_m1 n x,
        h5, pairInp_getD_T]

  have hgen : ∃ D : Circuit,
      GateOK (n + 2) D.gates ∧ D.output < n + 2 + D.gates.length ∧
      (∀ x : Finset (Fin n), wVal D.gates (inpVec n x) D.output = f x) ∧
      D.gates.length ≤ C.gates.length + 1 := by
    let rg := remapGates (n + m + 2) phiFix (n + 2) C.gates
    let rout := remapIdx (n + m + 2) phiFix (n + 2) C.output
    have hrgOK : GateOK (n + 2) rg := by
      have h0 := GateOK_remap (GateOK_nil (n + 2)) hCok phiFix hphiFix_W
      simpa [rg] using h0
    have hrgLen : rg.length = C.gates.length := by simp [rg, remapGates]
    have hrout_lt : rout < n + 2 + rg.length := by
      dsimp only [rout, remapIdx]
      split_ifs with hlt
      · have := hphiFix_W C.output hlt; simp at this; omega
      · rw [hrgLen]; omega
    obtain ⟨Dg, Dout, _, hDgOK, _, hDgLen, hDoutW, hDg_ev⟩ := mkNot_ex hrgOK hrout_lt
    refine ⟨⟨Dg, Dout⟩, hDgOK, hDoutW, ?_, by change Dg.length ≤ _; omega⟩
    intro x
    change wVal Dg (inpVec n x) Dout = f x
    rw [hDg_ev (inpVec n x) (inpVec_length n x)]
    have hrem := wVal_remap ([] : List Gate) phiFix hphiFix_W (inpVec n x) (pairInp n m x (preZ m k))
      (inpVec_length n x) (pairInp_length n m x (preZ m k)) (hphiFix_match x) C.gates hCok C.output hCout
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hrem
    rw [hrem, hCeval x (preZ m k)]
    unfold targetVal
    rw [card_preZ (by omega : k ≤ m)]
    dsimp only [k, h]
    simp only [lt_irrefl, ↓reduceIte, Bool.not_not]

  have hmono_ext : notCnt C.gates = b →
      ∃ D : Circuit,
        GateOK (n + 2) D.gates ∧ D.output < n + 2 + D.gates.length ∧
        (∀ x : Finset (Fin n), wVal D.gates (inpVec n x) D.output = f x) ∧
        PEqualNP.MetaComplexity.Monotone2 D ∧
        D.gates.length < C.gates.length := by
    intro hnotEq
    have h2eq : 2 ^ notCnt C.gates = 2 * h := by rw [hnotEq, h2b]
    have hphi_empty : phiC ∅ (preZ m k) = h - 1 := by omega
    have hphi_univ : phiC Finset.univ (preZ m k) = h := by omega
    have hphi_iff : ∀ x : Finset (Fin n), h ≤ phiC x (preZ m k) ↔ f x = true := by
      intro x
      cases hfx : f x with
      | false =>
        have hlt : phiC x (preZ m k) < phiC Finset.univ (preZ m k) := by
          apply hfall x Finset.univ (preZ m k) (preZ m k) (Finset.subset_univ x) (Finset.Subset.refl _)
          · unfold targetVal; rw [card_preZ (by omega : k ≤ m)]; simp [hfx]
          · unfold targetVal; rw [card_preZ (by omega : k ≤ m)]; simp [hf1]
        simp only [Bool.false_eq_true, iff_false]; omega
      | true =>
        have hlt : phiC ∅ (preZ m k) < phiC x (preZ m k) := by
          apply hfall ∅ x (preZ m k) (preZ m k) (Finset.empty_subset x) (Finset.Subset.refl _)
          · unfold targetVal; rw [card_preZ (by omega : k ≤ m)]; simp [hf0]
          · unfold targetVal; rw [card_preZ (by omega : k ≤ m)]; simp [hfx]
        simp only [iff_true]; omega
    have hpos_not : 0 < notCnt C.gates := by rw [hnotEq]; dsimp only [b]; omega
    obtain ⟨pre, g0, suf, hCsplit, hpre0, hg0not, hsuf_cnt⟩ := split_first_not C.gates hpos_not
    have hsuf_a : notCnt suf = a := by dsimp only [b] at hnotEq; omega
    have hpow_suf : 2 ^ notCnt suf = h := by rw [hsuf_a]
    have hbit_iff : ∀ x : Finset (Fin n),
        notInBit (evalWires pre (pairInp n m x (preZ m k))) g0 = 1 ↔ f x = true := by
      intro x
      rw [← hphi_iff x]
      dsimp only [phiC]
      rw [hCsplit, notCodeFrom_split_first pre suf g0 hpre0 hg0not, hpow_suf]
      have hrem : notCodeFrom (evalWires (pre ++ [g0]) (pairInp n m x (preZ m k))) suf < h := by
        rw [← hpow_suf]; exact notCodeFrom_lt suf _
      have hbit_le : notInBit (evalWires pre (pairInp n m x (preZ m k))) g0 ≤ 1 := by
        unfold notInBit; split_ifs <;> omega
      constructor <;> intro hh <;> nlinarith
    have hg0_nonempty : g0.inputs ≠ [] := by
      intro hem
      have h1 := (hbit_iff Finset.univ).2 hf1
      unfold notInBit at h1
      rw [hem] at h1
      simp at h1
    rcases List.exists_cons_of_ne_nil hg0_nonempty with ⟨u, rest, hu_eq⟩
    have hpreOK : GateOK (n + m + 2) pre := GateOK_prefix (by rw [← hCsplit]; exact hCok)
    have hu_lt : u < n + m + 2 + pre.length := by
      have hj : pre.length < C.gates.length := by rw [hCsplit]; simp
      have hget : C.gates.getD pre.length ⟨GateOp.or, []⟩ = g0 := by
        rw [hCsplit, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl]
        simp
      have humem : u ∈ (C.gates.getD pre.length ⟨GateOp.or, []⟩).inputs := by
        rw [hget, hu_eq]; simp
      exact hCok.2 pre.length hj u humem
    have hu_ev : ∀ x : Finset (Fin n), wVal pre (pairInp n m x (preZ m k)) u = f x := by
      intro x
      apply Bool.eq_iff_iff.2
      rw [← hbit_iff x]
      unfold notInBit wVal
      rw [hu_eq]
      simp only [List.map_cons, List.headD_cons]
      cases (evalWires pre (pairInp n m x (preZ m k))).getD u false <;> simp
    let Dgates := remapGates (n + m + 2) phiFix (n + 2) pre
    let Dout := remapIdx (n + m + 2) phiFix (n + 2) u
    have hDok : GateOK (n + 2) Dgates := by
      have h0 := GateOK_remap (GateOK_nil (n + 2)) hpreOK phiFix hphiFix_W
      simpa [Dgates] using h0
    have hDlen : Dgates.length = pre.length := by simp [Dgates, remapGates]
    have hDout_lt : Dout < n + 2 + Dgates.length := by
      dsimp only [Dout, remapIdx]
      split_ifs with hlt
      · have := hphiFix_W u hlt; simp at this; omega
      · rw [hDlen]; omega
    have hDmono : PEqualNP.MetaComplexity.Monotone2 ⟨Dgates, Dout⟩ :=
      Monotone2_remap (n + m + 2) phiFix (n + 2) pre (Monotone2_of_notCnt_zero pre hpreOK.1 hpre0)
    refine ⟨⟨Dgates, Dout⟩, hDok, hDout_lt, ?_, hDmono, ?_⟩
    · intro x
      change wVal Dgates (inpVec n x) Dout = f x
      have hrem := wVal_remap ([] : List Gate) phiFix hphiFix_W (inpVec n x) (pairInp n m x (preZ m k))
        (inpVec_length n x) (pairInp_length n m x (preZ m k)) (hphiFix_match x) pre hpreOK u hu_lt
      simp only [List.nil_append, List.length_nil, Nat.add_zero] at hrem
      rw [hrem, hu_ev x]
    · change Dgates.length < C.gates.length
      rw [hDlen, hCsplit]; simp
  exact ⟨hnot_ge, hgen, hmono_ext⟩

lemma log2_bound_1280 {a n : ℕ} (hn1 : 1 ≤ n) :
    let h := 2 ^ a
    let k := 2 * (h - 1)
    let m := 2 * k
    let P := 2 ^ (a + 2)
    4 * (a + 2) * (a + 2 + 1) * P + 16 * P ≤ 96 * (n + m + 2) * (Nat.log2 (n + m + 2) + 2) ^ 2 := by
  intro h k m P
  by_cases ha0 : a = 0
  · subst ha0
    have hm0 : m = 0 := by dsimp only [m, k, h]; decide
    have hP4 : P = 4 := by dsimp only [P]; decide
    have hlog1 : 1 ≤ Nat.log2 (n + 0 + 2) := (Nat.le_log2 (by omega)).2 (by omega)
    rw [hm0, hP4]
    have hsq : 9 ≤ (Nat.log2 (n + 0 + 2) + 2) ^ 2 := by nlinarith
    nlinarith
  · have ha1 : 1 ≤ a := by omega
    have hh2 : 2 ≤ h := by
      dsimp only [h]
      calc 2 = 2 ^ 1 := by decide
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by omega) ha1
    have hP4h : P = 4 * h := by dsimp only [P, h]; rw [pow_add]; ring
    have hm_eq : m = 4 * h - 4 := by dsimp only [m, k]; omega
    have hnm_ge : 4 * h - 1 ≤ n + m + 2 := by omega
    have hPle : P ≤ 2 * (n + m + 2) := by omega
    have h2b_le : 2 ^ (a + 1) ≤ n + m + 2 := by
      have h2a1 : 2 ^ (a + 1) = 2 * h := by dsimp only [h]; rw [pow_succ, Nat.mul_comm]
      omega
    have hlog_ge : a + 1 ≤ Nat.log2 (n + m + 2) := (Nat.le_log2 (by omega)).2 h2b_le
    have h1 : (a + 2) * (a + 2 + 1) ≤ (Nat.log2 (n + m + 2) + 2) ^ 2 := by nlinarith
    have h2 : 1 ≤ (Nat.log2 (n + m + 2) + 2) ^ 2 := by nlinarith
    nlinarith

lemma part2_len_bound {a n dL l0 l1 l2a l2 l3 l4 : ℕ} (hn1 : 1 ≤ n)
    (h0 : l0 = dL)
    (h1 : l1 ≤ l0 + (a + 2) * (a + 2 + 1) * 2 ^ (a + 2))
    (h2a : l2a = l1 + 1) (h2 : l2 = l2a + 1)
    (h3 : l3 ≤ l2 + 5 * 2 ^ (a + 1))
    (h4 : l4 ≤ l3 + 2 * (2 * 2 ^ a - 1)) :
    l4 ≤ dL + 96 * (n + 2 * (2 * (2 ^ a - 1)) + 2) * (Nat.log2 (n + 2 * (2 * (2 ^ a - 1)) + 2) + 2) ^ 2 := by
  have hlogb := log2_bound_1280 (a := a) hn1
  have hP4 : 2 ^ (a + 2) = 4 * 2 ^ a := by rw [pow_add]; ring
  have h2b : 2 ^ (a + 1) = 2 * 2 ^ a := by rw [pow_succ, Nat.mul_comm]
  have hpos : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hmul4 : 4 * (a + 2) * (a + 2 + 1) * 2 ^ (a + 2) = 4 * ((a + 2) * (a + 2 + 1) * 2 ^ (a + 2)) := by ring
  dsimp only at hlogb
  rw [hmul4] at hlogb
  omega

lemma part3_len_bound {a n dL l1 l2 l3 l4 l5 l6 l6a l7 : ℕ} (hn1 : 1 ≤ n)
    (h1 : l1 ≤ 0 + (a + 2) * (a + 2 + 1) * 2 ^ (a + 2))
    (h2 : l2 ≤ l1 + (a + 2) * (a + 2 + 1) * 2 ^ (a + 2))
    (h3 : l3 ≤ l2 + 5 * 2 ^ (a + 2))
    (h4 : l4 ≤ l3 + (2 ^ (a + 2) - 1))
    (h5 : l5 ≤ l4 + 2 * (a + 2) * (a + 2 + 1) * 2 ^ (a + 2))
    (h6 : l6 ≤ l5 + 2 * dL)
    (h6a : l6a = l6 + 1)
    (h7 : l7 ≤ l6a + 2 * (2 * 2 ^ a - 1)) :
    l7 ≤ 2 * dL + 96 * (n + 2 * (2 * (2 ^ a - 1)) + 2) * (Nat.log2 (n + 2 * (2 * (2 ^ a - 1)) + 2) + 2) ^ 2 := by
  have hlogb := log2_bound_1280 (a := a) hn1
  have hP4 : 2 ^ (a + 2) = 4 * 2 ^ a := by rw [pow_add]; ring
  have hpos : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have hmul4 : 4 * (a + 2) * (a + 2 + 1) * 2 ^ (a + 2) = 4 * ((a + 2) * (a + 2 + 1) * 2 ^ (a + 2)) := by ring
  have hmul2 : 2 * (a + 2) * (a + 2 + 1) * 2 ^ (a + 2) = 2 * ((a + 2) * (a + 2 + 1) * 2 ^ (a + 2)) := by ring
  dsimp only at hlogb
  rw [hmul4] at hlogb
  rw [hmul2] at h5
  omega

lemma count_true_padZ {n m P : ℕ} (_hmp : m ≤ P) (gs : List Gate)
    (x : Finset (Fin n)) (z : Finset (Fin m)) :
    let wF := n + m
    let padZ : List ℕ := List.ofFn (fun i : Fin m => n + i.val) ++ List.replicate (P - m) wF
    (padZ.map (wVal gs (pairInp n m x z))).count true = z.card := by
  intro wF padZ
  have hmap : padZ.map (wVal gs (pairInp n m x z)) =
      List.ofFn (fun i : Fin m => decide (i ∈ z)) ++ List.replicate (P - m) false := by
    simp only [padZ, List.map_append, List.map_ofFn, List.map_replicate]
    congr 1
    · apply List.ext_getElem (by simp)
      intro i hi1 _
      have him : i < m := by simp at hi1; exact hi1
      simp only [List.getElem_ofFn, Function.comp_apply]
      rw [evalWires_input gs (pairInp n m x z) (by rw [pairInp_length]; omega)]
      exact pairInp_getD_z n m x z ⟨i, him⟩
    · rw [evalWires_input gs (pairInp n m x z) (by rw [pairInp_length]; dsimp only [wF]; omega),
        pairInp_getD_F]
  rw [hmap, List.count_append, count_true_ofFn_mem]
  simp [List.count_replicate]

lemma exists_or_and_pairs {M : ℕ} (wF : ℕ) (hwF : wF < M)
    (ls rs : List ℕ) (hlen : ls.length = rs.length) :
    ∀ (cnt : ℕ) (_hcnt : cnt ≤ ls.length) (gs : List Gate), GateOK M gs →
      (∀ w ∈ ls, w < M + gs.length) → (∀ w ∈ rs, w < M + gs.length) →
      ∃ (gs' : List Gate) (outW : ℕ),
        Extends gs gs' ∧ GateOK M gs' ∧ notCnt gs' = notCnt gs ∧
        gs'.length ≤ gs.length + 2 * cnt ∧ outW < M + gs'.length ∧
        ∀ inp : List Bool, inp.length = M → inp.getD wF false = false →
          wVal gs' inp outW =
            decide (∃ i < cnt, wVal gs inp (ls.getD i 0) = true ∧ wVal gs inp (rs.getD i 0) = true) := by
  intro cnt
  induction cnt with
  | zero =>
    intro _ gs hgs _ _
    refine ⟨gs, wF, Extends.refl gs, hgs, rfl, by simp, by omega, ?_⟩
    intro inp hinp hF
    rw [evalWires_input gs inp (by omega), hF]
    simp
  | succ cnt ih =>
    intro hcnt gs hgs hlW hrW
    obtain ⟨gs1, acc, hext1, hgs1, hnc1, hlen1, haccW, hev1⟩ := ih (by omega) gs hgs hlW hrW
    have hl_m : ls.getD cnt 0 ∈ ls := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
    have hr_m : rs.getD cnt 0 ∈ rs := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
    have hle1 := hext1.length_le
    have hlc : ls.getD cnt 0 < M + gs1.length := by have := hlW _ hl_m; omega
    have hrc : rs.getD cnt 0 < M + gs1.length := by have := hrW _ hr_m; omega
    obtain ⟨gs2, wa, hx2, hgs2, hnc2, hlen2, hwaW, hev2⟩ := mkAnd_ex hgs1 hlc hrc
    obtain ⟨gs3, wo, hx3, hgs3, hnc3, hlen3, hwoW, hev3⟩ := mkOr_ex hgs2 (by omega : acc < M + gs2.length) hwaW
    refine ⟨gs3, wo, hext1.trans (hx2.trans hx3), hgs3, hnc3.trans (hnc2.trans hnc1), by omega, hwoW, ?_⟩
    intro inp hinp hF
    rw [hev3 inp hinp, hx2.wVal_eq inp (i := acc) (by omega), hev2 inp hinp,
      hev1 inp hinp hF,
      hext1.wVal_eq inp (i := ls.getD cnt 0) (by have := hlW _ hl_m; omega),
      hext1.wVal_eq inp (i := rs.getD cnt 0) (by have := hrW _ hr_m; omega)]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨i, hi, h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨i, by omega, h1, h2⟩
      · exact ⟨cnt, by omega, h1, h2⟩
    · rintro ⟨i, hi, h1, h2⟩
      by_cases hic : i < cnt
      · exact Or.inl ⟨i, hic, h1, h2⟩
      · have hieq : i = cnt := by omega
        rw [hieq] at h1 h2
        exact Or.inr ⟨h1, h2⟩

def vVal2 (a n m : ℕ) (f : Finset (Fin n) → Bool)
    (x : Finset (Fin n)) (z : Finset (Fin m)) : ℕ :=
  let h := 2 ^ a
  let k := 2 * (h - 1)
  if z.card < k then (z.card + 1) / 2
  else if z.card = k then (if f x then h else h - 1)
  else h + (z.card - k) / 2

lemma L_lib_1280_part2 (a n : ℕ)
    (f : Finset (Fin n) → Bool)
    (hf0 : f ∅ = false) (hf1 : f Finset.univ = true)
    (D : Circuit)
    (hDok : GateOK (n + 2) D.gates)
    (hDout : D.output < n + 2 + D.gates.length)
    (hDeval : ∀ x : Finset (Fin n), wVal D.gates (inpVec n x) D.output = f x)
    (hDmono : PEqualNP.MetaComplexity.Monotone2 D) :
    let h := 2 ^ a
    let b := a + 1
    let k := 2 * (h - 1)
    let m := 2 * k
    let K := 96 * (n + m + 2) * (Nat.log2 (n + m + 2) + 2) ^ 2
    ∃ C : Circuit,
      GateOK (n + m + 2) C.gates ∧ C.output < n + m + 2 + C.gates.length ∧
      (∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
        wVal C.gates (pairInp n m x z) C.output = targetVal k n m f x z) ∧
      notCnt C.gates = b ∧
      C.gates.length ≤ D.gates.length + K := by
  intro h b k m K
  have hn1 : 1 ≤ n := pos_n_of_ne_const f hf0 hf1
  have hh_pos : 1 ≤ h := Nat.one_le_two_pow
  have h2b : 2 ^ b = 2 * h := by dsimp only [b, h]; rw [pow_succ, Nat.mul_comm]
  let M := n + m + 2
  let wF := n + m
  let wT := n + m + 1
  let P := 2 ^ (a + 2)
  have hP4h : P = 4 * h := by dsimp only [P, h]; rw [pow_add]; ring
  have hm_lt_P : m < P := by dsimp only [m, k]; omega

  let psi : ℕ → ℕ := fun i => if i < n then i else if i = n then wF else wT
  have hpsiW : ∀ i < n + 2, psi i < M + ([] : List Gate).length := by
    intro i hi; dsimp only [psi, wF, wT, M]
    split_ifs <;> (simp only [List.length_nil, Nat.add_zero]; omega)
  let gs0 := remapGates (n + 2) psi M D.gates
  let fW := remapIdx (n + 2) psi M D.output
  have hgs0OK : GateOK M gs0 := by
    have h0 := GateOK_remap (GateOK_nil M) hDok psi hpsiW
    simpa [gs0] using h0
  have hgs0Len : gs0.length = D.gates.length := by simp [gs0, remapGates]
  have hgs0Not : notCnt gs0 = 0 := by
    have hmono0 := Monotone2_remap (n + 2) psi M D.gates hDmono
    unfold notCnt
    have hem : gs0.filter (fun g => isNotOp g.op) = [] := by
      apply List.filter_eq_nil_iff.2
      intro g hg
      have hmem := (hmono0 g hg).1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h1 | h1 <;> simp [isNotOp, h1]
    rw [hem]; rfl
  have hfW_lt : fW < M + gs0.length := by
    dsimp only [fW, remapIdx]
    split_ifs with hlt
    · have := hpsiW D.output hlt; simp at this; omega
    · rw [hgs0Len]; omega
  have hfW_ev : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      wVal gs0 (pairInp n m x z) fW = f x := by
    intro x z
    have hmatch : ∀ i < n + 2, wVal [] (pairInp n m x z) (psi i) = (inpVec n x).getD i false := by
      intro i hi; dsimp only [psi]
      split_ifs with h1 h2
      · rw [evalWires_input [] (pairInp n m x z) (by rw [pairInp_length]; omega),
          pairInp_getD_x n m x z ⟨i, h1⟩, inpVec_getD_lt n x ⟨i, h1⟩]
      · rw [evalWires_input [] (pairInp n m x z) (by rw [pairInp_length]; dsimp only [wF]; omega),
          pairInp_getD_F, h2, inpVec_getD_m]
      · have h3 : i = n + 1 := by omega
        rw [evalWires_input [] (pairInp n m x z) (by rw [pairInp_length]; dsimp only [wT]; omega),
          pairInp_getD_T, h3, inpVec_getD_m1]
    have hrem := wVal_remap ([] : List Gate) psi hpsiW (pairInp n m x z) (inpVec n x)
      (pairInp_length n m x z) (inpVec_length n x) hmatch D.gates hDok D.output hDout
    simp only [List.nil_append, List.length_nil, Nat.add_zero] at hrem
    rw [hrem, hDeval x]

  let padZ : List ℕ := List.ofFn (fun i : Fin m => n + i.val) ++ List.replicate (P - m) wF
  have hpadZ_len : padZ.length = 2 ^ (a + 2) := by simp [padZ, P]; omega
  have hpadZ_W : ∀ w ∈ padZ, w < M + gs0.length := by
    intro w hw
    simp only [padZ, List.mem_append, List.mem_ofFn, List.mem_replicate] at hw
    rcases hw with ⟨i, rfl⟩ | ⟨_, rfl⟩ <;> dsimp only [M, wF] <;> omega
  obtain ⟨gs1, ysZ, hext01, hgs1, hnc1, hlen1, hysZl, hysZW, hsortZ_ev, _, _⟩ :=
    exists_sort_full (m := M) wF (by dsimp only [wF, M]; omega) (a + 2) gs0 padZ hgs0OK hpadZ_len hpadZ_W
  let geZ : ℕ → ℕ := fun t => if t = 0 then wT else if t ≤ m then ysZ.getD (t - 1) 0 else wF
  have hgeZ_W : ∀ t : ℕ, geZ t < M + gs1.length := by
    intro t; dsimp only [geZ]
    split_ifs with h0 hle
    · dsimp only [wT, M]; omega
    · have hm : ysZ.getD (t - 1) 0 ∈ ysZ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      exact hysZW _ hm
    · dsimp only [wF, M]; omega
  have hgeZ_ev : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (t : ℕ),
      wVal gs1 (pairInp n m x z) (geZ t) = decide (t ≤ z.card) := by
    intro x z t
    dsimp only [geZ]
    split_ifs with h0 hle
    · rw [h0, evalWires_input gs1 (pairInp n m x z) (by rw [pairInp_length]; dsimp only [wT]; omega),
        pairInp_getD_T]; simp
    · have hs := hsortZ_ev (pairInp n m x z) (pairInp_length n m x z)
      have hget := getElem_isSortedDesc hs.1 (i := t - 1) (by simp [hysZl]; omega)
      simp only [List.getElem_map] at hget
      rw [hs.2, count_true_padZ (by omega : m ≤ P) gs0 x z] at hget
      have hgt : ysZ.getD (t - 1) 0 = ysZ[t - 1]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hgt, hget]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]; omega
    · rw [evalWires_input gs1 (pairInp n m x z) (by rw [pairInp_length]; dsimp only [wF]; omega),
        pairInp_getD_F]
      have hcz : z.card ≤ m := by
        calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ z
          _ = m := by simp
      symm; simp only [decide_eq_false_iff_not]; omega

  have hfW1 : fW < M + gs1.length := by have := hext01.length_le; omega
  obtain ⟨gs2a, wkf, hx1_2a, hgs2a, hnc2a, hlen2a, hwkfW, hev2a⟩ := mkAnd_ex hgs1 (hgeZ_W k) hfW1
  obtain ⟨gs2, wTh, hx2a_2, hgs2, hnc2, hlen2, hwThW, hev2⟩ :=
    mkOr_ex hgs2a (by have := hx1_2a.length_le; have := hgeZ_W (k + 1); omega : geZ (k + 1) < M + gs2a.length) hwkfW
  have hext12 : Extends gs1 gs2 := hx1_2a.trans hx2a_2
  have hwTh_ev : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      wVal gs2 (pairInp n m x z) wTh = decide (k + 1 ≤ z.card ∨ (k ≤ z.card ∧ f x = true)) := by
    intro x z
    have hinp := pairInp_length n m x z
    rw [hev2 (pairInp n m x z) hinp,
      hx1_2a.wVal_eq (pairInp n m x z) (i := geZ (k + 1)) (by rw [hinp]; exact hgeZ_W (k + 1)),
      hev2a (pairInp n m x z) hinp,
      hgeZ_ev x z (k + 1), hgeZ_ev x z k,
      hext01.wVal_eq (pairInp n m x z) (i := fW) (by rw [hinp]; exact hfW_lt),
      hfW_ev x z]
    apply Bool.eq_iff_iff.2
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
  let T : List ℕ := List.ofFn fun j : Fin (2 ^ b) =>
    if j.val = 0 then wF
    else if j.val < h then geZ (2 * j.val - 1)
    else if j.val = h then wTh
    else geZ (k + 2 * (j.val - (h + 1)) + 2)
  have hTl : T.length = 2 ^ b := by simp [T]
  have hTW : ∀ w ∈ T, w < M + gs2.length := by
    intro w hw; simp only [T, List.mem_ofFn] at hw
    rcases hw with ⟨j, rfl⟩
    split_ifs
    · dsimp only [wF, M]; omega
    · have := hext12.length_le; have := hgeZ_W (2 * j.val - 1); omega
    · exact hwThW
    · have := hext12.length_le; have := hgeZ_W (k + 2 * (j.val - (h + 1)) + 2); omega
  have hvVal_lt : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)), vVal2 a n m f x z < 2 ^ b := by
    intro x z
    have hcz : z.card ≤ m := by
      calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ z
        _ = m := by simp
    unfold vVal2; dsimp only [m, k, h] at hcz ⊢
    split_ifs <;> omega
  have hT_ev : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (j : ℕ), 1 ≤ j → j < 2 ^ b →
      wVal gs2 (pairInp n m x z) (T.getD j 0) = decide (j ≤ vVal2 a n m f x z) := by
    intro x z j hj1 hjb
    have hgt : T.getD j 0 =
        if j < h then geZ (2 * j - 1) else if j = h then wTh else geZ (k + 2 * (j - (h + 1)) + 2) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : j < T.length)]
      simp [T, show j ≠ 0 by omega]
    rw [hgt]
    have hinp := pairInp_length n m x z
    split_ifs with hlt heq
    · rw [hext12.wVal_eq (pairInp n m x z) (by rw [hinp]; exact hgeZ_W _), hgeZ_ev x z]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
      unfold vVal2; dsimp only [k, h] at hlt ⊢
      split_ifs <;> omega
    · rw [heq, hwTh_ev x z]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
      unfold vVal2; dsimp only [k, h]
      by_cases h1 : z.card < 2 * (2 ^ a - 1)
      · simp only [h1, ↓reduceIte]; omega
      · by_cases h2 : z.card = 2 * (2 ^ a - 1)
        · simp only [h2, lt_irrefl, ↓reduceIte]
          cases hfx : f x <;> simp
        · simp only [h1, h2, ↓reduceIte]; omega
    · rw [hext12.wVal_eq (pairInp n m x z) (by rw [hinp]; exact hgeZ_W _), hgeZ_ev x z]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]
      unfold vVal2; dsimp only [k, h] at hlt heq ⊢
      split_ifs <;> omega

  obtain ⟨gs3, eqV, hext23, hgs3, hnc3, hlen3, heqVl, heqVW, heqV_ev⟩ :=
    exists_b_decoder_aux b wF wT (by dsimp only [wF, M]; omega) (by dsimp only [wT, M]; omega)
      T hTl b le_rfl gs2 hgs2 hTW

  let rLen := 2 * h - 1
  let Llist : List ℕ := List.ofFn fun i : Fin rLen =>
    if i.val + 1 ≤ h then geZ (2 * i.val) else geZ (k + 2 * (i.val - h) + 1)
  let Rlist : List ℕ := List.ofFn fun i : Fin rLen => eqV.getD i.val 0
  have hLRlen : Llist.length = Rlist.length := by simp [Llist, Rlist]
  have hext13 : Extends gs1 gs3 := hext12.trans hext23
  have hLW : ∀ w ∈ Llist, w < M + gs3.length := by
    intro w hw; simp only [Llist, List.mem_ofFn] at hw
    rcases hw with ⟨i, rfl⟩
    split_ifs
    · have := hext13.length_le; have := hgeZ_W (2 * i.val); omega
    · have := hext13.length_le; have := hgeZ_W (k + 2 * (i.val - h) + 1); omega
  have hRW : ∀ w ∈ Rlist, w < M + gs3.length := by
    intro w hw; simp only [Rlist, List.mem_ofFn] at hw
    rcases hw with ⟨i, rfl⟩
    have hm : eqV.getD i.val 0 ∈ eqV := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by dsimp only [rLen] at i; omega)]
      exact List.getElem_mem _
    exact heqVW _ hm
  obtain ⟨gs4, outW, hext34, hgs4, hnc4, hlen4, houtW, hev4⟩ :=
    exists_or_and_pairs wF (by dsimp only [wF, M]; omega) Llist Rlist hLRlen rLen (by simp [Llist]) gs3 hgs3 hLW hRW
  have hnot_tot : notCnt gs4 = b := by
    rw [hnc4, hnc3, hnc2, hnc2a, hnc1, hgs0Not]; omega
  have hlen_tot : gs4.length ≤ D.gates.length + K :=
    part2_len_bound hn1 hgs0Len hlen1 hlen2a hlen2 hlen3 hlen4
  refine ⟨⟨gs4, outW⟩, hgs4, houtW, ?_, hnot_tot, hlen_tot⟩
  intro x z
  change wVal gs4 (pairInp n m x z) outW = targetVal k n m f x z
  have hinp := pairInp_length n m x z
  rw [hev4 (pairInp n m x z) hinp (pairInp_getD_F n m x z)]
  have hcz : z.card ≤ m := by
    calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ z
      _ = m := by simp
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_eq]
  have hpair_ev : ∀ i < rLen,
      (wVal gs3 (pairInp n m x z) (Llist.getD i 0) = true ∧
       wVal gs3 (pairInp n m x z) (Rlist.getD i 0) = true) ↔
      ((if i + 1 ≤ h then 2 * i ≤ z.card else k + 2 * (i - h) + 1 ≤ z.card) ∧
       vVal2 a n m f x z = i) := by
    intro i hi
    have hLgt : Llist.getD i 0 = if i + 1 ≤ h then geZ (2 * i) else geZ (k + 2 * (i - h) + 1) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Llist]; exact hi)]
      simp [Llist]
    have hRgt : Rlist.getD i 0 = eqV.getD i 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Rlist]; exact hi)]
      simp [Rlist]
    rw [hLgt, hRgt]
    have hR : wVal gs3 (pairInp n m x z) (eqV.getD i 0) = decide (vVal2 a n m f x z = i) := by
      have h := heqV_ev (pairInp n m x z) (vVal2 a n m f x z) hinp
        (pairInp_getD_F n m x z) (pairInp_getD_T n m x z) (hvVal_lt x z) (hT_ev x z) i
        (by dsimp only [rLen] at hi; omega)
      simpa using h
    rw [hR]
    split_ifs with hih
    · rw [hext13.wVal_eq (pairInp n m x z) (by rw [hinp]; exact hgeZ_W _), hgeZ_ev x z]
      simp [decide_eq_true_eq]
    · rw [hext13.wVal_eq (pairInp n m x z) (by rw [hinp]; exact hgeZ_W _), hgeZ_ev x z]
      simp [decide_eq_true_eq]
  have hiff_ex : (∃ i < rLen, wVal gs3 (pairInp n m x z) (Llist.getD i 0) = true ∧
      wVal gs3 (pairInp n m x z) (Rlist.getD i 0) = true) ↔
      (∃ i < rLen, (if i + 1 ≤ h then 2 * i ≤ z.card else k + 2 * (i - h) + 1 ≤ z.card) ∧
        vVal2 a n m f x z = i) := by
    constructor
    · rintro ⟨i, hi, hp⟩; exact ⟨i, hi, (hpair_ev i hi).1 hp⟩
    · rintro ⟨i, hi, hp⟩; exact ⟨i, hi, (hpair_ev i hi).2 hp⟩
  rw [hiff_ex]
  unfold targetVal vVal2
  have hh1 : 1 ≤ 2 ^ a := hh_pos
  dsimp only [rLen, m, k, h] at hcz ⊢
  by_cases hlt : z.card < 2 * (2 ^ a - 1)
  · simp only [hlt, ↓reduceIte, decide_eq_true_eq]
    constructor
    · rintro ⟨i, _, hL, heq⟩
      have hi_le : i + 1 ≤ 2 ^ a := by omega
      simp only [hi_le, ↓reduceIte] at hL; omega
    · intro hev
      refine ⟨(z.card + 1) / 2, by omega, ?_, rfl⟩
      have hi_le : (z.card + 1) / 2 + 1 ≤ 2 ^ a := by omega
      simp only [hi_le, ↓reduceIte]; omega
  · by_cases heq : z.card = 2 * (2 ^ a - 1)
    · simp only [heq, lt_irrefl, ↓reduceIte]
      cases hfx : f x with
      | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, iff_true]
        refine ⟨2 ^ a - 1, by omega, ?_, rfl⟩
        simp only [show 2 ^ a - 1 + 1 ≤ 2 ^ a by omega, ↓reduceIte]; omega
      | true =>
        simp only [↓reduceIte, Bool.not_true, Bool.false_eq_true, iff_false, not_exists, not_and]
        intro i hi hL hv
        have hi_gt : ¬ (i + 1 ≤ 2 ^ a) := by omega
        simp only [hi_gt, ↓reduceIte] at hL; omega
    · simp only [hlt, heq, ↓reduceIte, decide_eq_true_eq]
      constructor
      · rintro ⟨i, hi, hL, hv⟩
        have hi_gt : ¬ (i + 1 ≤ 2 ^ a) := by omega
        simp only [hi_gt, ↓reduceIte] at hL; omega
      · intro hodd
        refine ⟨2 ^ a + (z.card - 2 * (2 ^ a - 1)) / 2, by omega, ?_, rfl⟩
        have hi_gt : ¬ (2 ^ a + (z.card - 2 * (2 ^ a - 1)) / 2 + 1 ≤ 2 ^ a) := by omega
        simp only [hi_gt, ↓reduceIte]; omega

lemma count_true_lt_of_last_false {L : List Bool} (hpos : 0 < L.length)
    (hlast : L.getD (L.length - 1) true = false) : L.count true < L.length := by
  have htake : L = L.take (L.length - 1) ++ [L.getD (L.length - 1) true] := by
    apply List.ext_getElem
    · simp; omega
    · intro i hi1 hi2
      by_cases hlt : i < L.length - 1
      · rw [List.getElem_append_left (by simp; omega), List.getElem_take]
      · have hieq : i = L.length - 1 := by omega
        rw [List.getElem_append_right (by simp; omega)]
        have hidx : i - (L.take (L.length - 1)).length = 0 := by simp; omega
        simp only [hidx, List.getElem_cons_zero, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by omega : L.length - 1 < L.length), Option.getD_some]
        congr 1
  conv_lhs => rw [htake, hlast]
  rw [List.count_append]
  have hle := count_true_le_length (L.take (L.length - 1))
  simp only [List.length_take] at hle
  have h0 : [false].count true = 0 := by decide
  rw [h0]
  omega

lemma part3_target_iff (H c : ℕ) (fx : Bool) (hH : 1 ≤ H) (hc : c ≤ 2 * (2 * (H - 1))) :
    (∃ i < 2 * H - 1,
      (if i + 1 ≤ H then 2 * i ≤ c else 2 * (H - 1) + 2 * (i - H) + 1 ≤ c) ∧
      c < (if i + 1 < H then 2 * i + 1 else if i + 1 = H then 2 * (H - 1) + 1 else 2 * (H - 1) + 2 * (i - H) + 2) ∧
      (i + 1 = H → fx = false)) ↔
    (if c < 2 * (H - 1) then decide (c % 2 = 0)
     else if c = 2 * (H - 1) then !fx else decide (c % 2 = 1)) = true := by
  by_cases hlt : c < 2 * (H - 1)
  · simp only [hlt, ↓reduceIte, decide_eq_true_eq]
    constructor
    · rintro ⟨i, _, hL, hR, _⟩
      split_ifs at hL hR <;> omega
    · intro hev
      refine ⟨c / 2, by omega, ?_, ?_, fun hh => by omega⟩
      · simp only [show c / 2 + 1 ≤ H by omega, ↓reduceIte]; omega
      · simp only [show c / 2 + 1 < H by omega, ↓reduceIte]; omega
  · by_cases heq : c = 2 * (H - 1)
    · simp only [heq, lt_irrefl, ↓reduceIte, Bool.not_eq_true']
      constructor
      · rintro ⟨i, _, hL, hR, hfx⟩
        have hieq : i + 1 = H := by split_ifs at hL hR <;> omega
        exact hfx hieq
      · intro hfx
        refine ⟨H - 1, by omega, ?_, ?_, fun _ => hfx⟩
        · simp only [show H - 1 + 1 ≤ H by omega, ↓reduceIte]; omega
        · simp only [show H - 1 + 1 = H by omega, lt_irrefl, ↓reduceIte]; omega
    · simp only [hlt, heq, ↓reduceIte, decide_eq_true_eq]
      constructor
      · rintro ⟨i, _, hL, hR, _⟩
        split_ifs at hL hR <;> omega
      · intro hodd
        refine ⟨H + (c - 2 * (H - 1) - 1) / 2, by omega, ?_, ?_, fun hh => by omega⟩
        · simp only [show ¬ (H + (c - 2 * (H - 1) - 1) / 2 + 1 ≤ H) by omega, ↓reduceIte]; omega
        · simp only [show ¬ (H + (c - 2 * (H - 1) - 1) / 2 + 1 < H) by omega,
            show H + (c - 2 * (H - 1) - 1) / 2 + 1 ≠ H by omega, ↓reduceIte]; omega

lemma L_lib_1280_part3 (a n : ℕ) (hn : n ≤ 2 * 2 ^ a)
    (f : Finset (Fin n) → Bool)
    (hf0 : f ∅ = false) (hf1 : f Finset.univ = true)
    (D : Circuit)
    (hDok : GateOK (n + 2) D.gates)
    (hDout : D.output < n + 2 + D.gates.length)
    (hDeval : ∀ x : Finset (Fin n), wVal D.gates (inpVec n x) D.output = f x) :
    let h := 2 ^ a
    let b := a + 1
    let k := 2 * (h - 1)
    let m := 2 * k
    let K := 96 * (n + m + 2) * (Nat.log2 (n + m + 2) + 2) ^ 2
    ∃ C : Circuit,
      GateOK (n + m + 2) C.gates ∧ C.output < n + m + 2 + C.gates.length ∧
      (∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
        wVal C.gates (pairInp n m x z) C.output = targetVal k n m f x z) ∧
      notCnt C.gates = b + 1 ∧
      C.gates.length ≤ 2 * D.gates.length + K := by
  intro h b k m K
  have hn1 : 1 ≤ n := pos_n_of_ne_const f hf0 hf1
  have hh_pos : 1 ≤ h := Nat.one_le_two_pow
  let M := n + m + 2
  let wF := n + m
  let wT := n + m + 1
  let P := 2 ^ (b + 1)
  have hP4h : P = 4 * h := by dsimp only [P, b, h]; rw [pow_add]; ring
  have hm_lt_P : m < P := by dsimp only [m, k]; omega
  have hwF : wF < M := by dsimp only [wF, M]; omega
  have hwT : wT < M := by dsimp only [wT, M]; omega

  let padZ : List ℕ := List.ofFn (fun i : Fin m => n + i.val) ++ List.replicate (P - m) wF
  have hpadZ_len : padZ.length = 2 ^ (b + 1) := by
    simp only [padZ, List.length_append, List.length_ofFn, List.length_replicate]
    dsimp only [P] at hm_lt_P ⊢; omega
  have hpadZ_W : ∀ w ∈ padZ, w < M + ([] : List Gate).length := by
    intro w hw
    simp only [padZ, List.mem_append, List.mem_ofFn, List.mem_replicate] at hw
    rcases hw with ⟨i, rfl⟩ | ⟨_, rfl⟩ <;> dsimp only [M, wF] <;> omega
  obtain ⟨gs1, ysZ, hext01, hgs1, hnc1, hlen1, hysZl, hysZW, hsortZ_ev, _, _⟩ :=
    exists_sort_full (m := M) wF hwF (b + 1) [] padZ (GateOK_nil M) hpadZ_len hpadZ_W
  let geZ : ℕ → ℕ := fun t => if t = 0 then wT else if t ≤ m then ysZ.getD (t - 1) 0 else wF
  have hgeZ_W : ∀ t : ℕ, geZ t < M + gs1.length := by
    intro t; dsimp only [geZ]
    split_ifs with h0 hle
    · omega
    · have hm : ysZ.getD (t - 1) 0 ∈ ysZ := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      exact hysZW _ hm
    · omega
  have hgeZ_ev : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (t : ℕ),
      wVal gs1 (pairInp n m x z) (geZ t) = decide (t ≤ z.card) := by
    intro x z t
    dsimp only [geZ]
    split_ifs with h0 hle
    · rw [h0, evalWires_input gs1 (pairInp n m x z) (by rw [pairInp_length]; omega),
        pairInp_getD_T]; simp
    · have hs := hsortZ_ev (pairInp n m x z) (pairInp_length n m x z)
      have hget := getElem_isSortedDesc hs.1 (i := t - 1) (by simp [hysZl]; omega)
      simp only [List.getElem_map] at hget
      rw [hs.2, count_true_padZ (by omega : m ≤ P) [] x z] at hget
      have hgt : ysZ.getD (t - 1) 0 = ysZ[t - 1]'(by omega) := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      rw [hgt, hget]
      apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]; omega
    · rw [evalWires_input gs1 (pairInp n m x z) (by rw [pairInp_length]; omega), pairInp_getD_F]
      have hcz : z.card ≤ m := by
        calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ z
          _ = m := by simp
      symm; simp only [decide_eq_false_iff_not]; omega

  let rLen := 2 * h - 1
  let eThr : ℕ → ℕ := fun i =>
    if i + 1 < h then 2 * i + 1
    else if i + 1 = h then k + 1
    else k + 2 * (i - h) + 2
  let W : List ℕ := List.ofFn fun idx : Fin P =>
    if idx.val < n then idx.val
    else if idx.val < n + rLen then geZ (eThr (idx.val - n))
    else wF
  have hWl : W.length = 2 ^ (b + 1) := by simp [W, P]
  have hWW : ∀ w ∈ W, w < M + gs1.length := by
    intro w hw; simp only [W, List.mem_ofFn] at hw
    rcases hw with ⟨idx, rfl⟩
    split_ifs
    · dsimp only [M]; omega
    · exact hgeZ_W _
    · omega
  have hW_cnt_lt : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      (W.map (wVal gs1 (pairInp n m x z))).count true < 2 ^ (b + 1) := by
    intro x z
    have hlt := count_true_lt_of_last_false (L := W.map (wVal gs1 (pairInp n m x z)))
      (by simp [hWl]) (by
        have hlenM : (W.map (wVal gs1 (pairInp n m x z))).length = P := by simp [hWl, P]
        rw [hlenM, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (by simp [hWl]; dsimp only [P]; omega)]
        simp only [Option.getD_some, List.getElem_map]
        have hlastW : W[P - 1]'(by omega) = wF := by
          simp only [W, List.getElem_ofFn]
          have h1 : ¬ (P - 1 < n) := by omega
          have h2 : ¬ (P - 1 < n + rLen) := by dsimp only [rLen]; omega
          simp [h1, h2]
        rw [hlastW, evalWires_input gs1 (pairInp n m x z) (by rw [pairInp_length]; omega), pairInp_getD_F])
    simpa [hWl] using hlt

  obtain ⟨gs2, ysW, hext12, hgs2, hnc2, hlen2, hysWl, hysWW, hsortW_ev, hsortW_rev, _⟩ :=
    exists_sort_full (m := M) wF hwF (b + 1) gs1 W hgs1 hWl hWW
  let TW : List ℕ := List.ofFn fun t : Fin (2 ^ (b + 1)) =>
    if t.val = 0 then wF else ysW.getD (t.val - 1) 0
  have hTWl : TW.length = 2 ^ (b + 1) := by simp [TW]
  have hTWW : ∀ w ∈ TW, w < M + gs2.length := by
    intro w hw; simp only [TW, List.mem_ofFn] at hw
    rcases hw with ⟨t, rfl⟩
    split_ifs with h0
    · omega
    · have hm : ysW.getD (t.val - 1) 0 ∈ ysW := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      exact hysWW _ hm
  obtain ⟨gs3, eqW, hext23, hgs3, hnc3, hlen3, heqWl, heqWW, heqW_ev⟩ :=
    exists_b_decoder_aux (b + 1) wF wT hwF hwT TW hTWl (b + 1) le_rfl gs2 hgs2 hTWW
  obtain ⟨gs4, leW, hext34, hgs4, hnc4, hlen4, hleWl, hleWW, hleW_ev⟩ :=
    exists_prefix_or eqW (P - 1) (by dsimp only [P]; omega) gs3 hgs3 heqWW
  have hext24 : Extends gs2 gs4 := hext23.trans hext34
  obtain ⟨gs5, negW, hext45, hgs5, hnc5, hlen5, hnegWl, hnegWW, hnegW_ev⟩ :=
    hsortW_rev gs4 leW hext24 hgs4 (by dsimp only [P] at hleWl; omega) hleWW
  have hnegW_spec : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)) (idx : ℕ), idx < P →
      wVal gs5 (pairInp n m x z) (negW.getD idx 0) = !(wVal gs1 (pairInp n m x z) (W.getD idx 0)) := by
    intro x z idx hidx
    have hinp := pairInp_length n m x z
    have hle_eq : leW.map (wVal gs4 (pairInp n m x z)) = (ysW.map (wVal gs2 (pairInp n m x z))).map (!·) := by
      apply List.ext_getElem
      · simp only [List.length_map, hleWl, hysWl]; dsimp only [P] at hP4h ⊢; omega
      · intro t ht1 _
        have htp : t < P := by simp [hleWl] at ht1; dsimp only [P] at *; omega
        simp only [List.getElem_map]
        have hgt_le : leW[t]'(by omega) = leW.getD t 0 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
        rw [hgt_le, hleW_ev (pairInp n m x z) hinp t (by omega)]
        have hs := hsortW_ev (pairInp n m x z) hinp
        have hys_t := getElem_isSortedDesc hs.1 (i := t) (by simp [hysWl]; exact htp)
        simp only [List.getElem_map] at hys_t
        rw [hys_t, hs.2]
        let cW := (W.map (wVal gs1 (pairInp n m x z))).count true
        have hcW_lt : cW < 2 ^ (b + 1) := hW_cnt_lt x z
        have hTspec : ∀ u, 1 ≤ u → u < 2 ^ (b + 1) →
            wVal gs2 (pairInp n m x z) (TW.getD u 0) = decide (u ≤ cW) := by
          intro u hu1 hup
          have hgt : TW.getD u 0 = ysW.getD (u - 1) 0 := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : u < TW.length)]
            simp [TW, show u ≠ 0 by omega]
          rw [hgt]
          have hget := getElem_isSortedDesc hs.1 (i := u - 1) (by simp [hysWl]; omega)
          simp only [List.getElem_map] at hget
          have hgt2 : ysW.getD (u - 1) 0 = ysW[u - 1]'(by omega) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
          rw [hgt2, hget, hs.2]
          apply Bool.eq_iff_iff.2; simp only [decide_eq_true_eq]; omega
        apply Bool.eq_iff_iff.2
        simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not]
        constructor
        · rintro ⟨i, hit, hi_ev⟩
          have h := heqW_ev (pairInp n m x z) cW hinp (pairInp_getD_F n m x z) (pairInp_getD_T n m x z)
            hcW_lt hTspec i (by dsimp only [P] at htp; omega)
          simp only [Nat.sub_self, pow_zero, Nat.div_one] at h
          rw [h, decide_eq_true_eq] at hi_ev; omega
        · intro hnotlt
          refine ⟨cW, by omega, ?_⟩
          have h := heqW_ev (pairInp n m x z) cW hinp (pairInp_getD_F n m x z) (pairInp_getD_T n m x z)
            hcW_lt hTspec cW hcW_lt
          simp only [Nat.sub_self, pow_zero, Nat.div_one] at h
          rw [h]; simp
    have hmap := hnegW_ev (pairInp n m x z) hinp hle_eq
    have hget := congrArg (fun L => L.getD idx false) hmap
    have hL : (negW.map (wVal gs5 (pairInp n m x z))).getD idx false =
        wVal gs5 (pairInp n m x z) (negW.getD idx 0) := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp [hnegWl]; exact hidx),
          List.getElem?_eq_getElem (by omega : idx < negW.length)]
      simp
    have hR : ((W.map (wVal gs1 (pairInp n m x z))).map (!·)).getD idx false =
        !(wVal gs1 (pairInp n m x z) (W.getD idx 0)) := by
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_getElem (by simp [hWl]; exact hidx),
          List.getElem?_eq_getElem (by omega : idx < W.length)]
      simp
    rw [← hL, hget, hR]

  let drInit : List (ℕ × ℕ) :=
    List.ofFn (fun i : Fin n => (i.val, negW.getD i.val 0)) ++ [(wF, wT), (wT, wF)]
  have hdrInit_len : drInit.length = n + 2 := by simp [drInit]
  have hdrInit_W : ∀ p ∈ drInit, p.1 < M + gs5.length ∧ p.2 < M + gs5.length := by
    intro p hp
    simp only [drInit, List.mem_append, List.mem_ofFn, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with ⟨i, rfl⟩ | rfl | rfl
    · have hm : negW.getD i.val 0 ∈ negW := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
      exact ⟨by dsimp only [M]; omega, hnegWW _ hm⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
  obtain ⟨gs6, drOut, hext56, hgs6, hnc6, hlen6, hdrOut_len, hdrOut_W, hdrOut_ev⟩ :=
    exists_sim_D_mono_aux wF wT hwF hwT D.gates gs5 drInit hgs5 hDok.1
      (by rw [hdrInit_len]; exact hDok.2) hdrInit_W
  let notFx := (drOut.getD D.output (0, 0)).2
  have hnotFx_m : drOut.getD D.output (0, 0) ∈ drOut := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hnotFx_W : notFx < M + gs6.length := (hdrOut_W _ hnotFx_m).2
  have hnotFx_ev : ∀ (x : Finset (Fin n)) (z : Finset (Fin m)),
      wVal gs6 (pairInp n m x z) notFx = !(f x) := by
    intro x z
    have hinp := pairInp_length n m x z
    have hagree : ∀ i < drInit.length,
        wVal gs5 (pairInp n m x z) (drInit.getD i (0, 0)).1 = (inpVec n x).getD i false ∧
        wVal gs5 (pairInp n m x z) (drInit.getD i (0, 0)).2 = !((inpVec n x).getD i false) := by
      intro i hi
      by_cases h1 : i < n
      · have hgt : drInit.getD i (0, 0) = (i, negW.getD i 0) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
          simp only [drInit, Option.getD_some]
          rw [List.getElem_append_left (by simp [h1])]; simp
        rw [hgt, evalWires_input gs5 (pairInp n m x z) (by rw [hinp]; omega),
          pairInp_getD_x n m x z ⟨i, h1⟩, inpVec_getD_lt n x ⟨i, h1⟩,
          hnegW_spec x z i (by omega)]
        have hWi : W.getD i 0 = i := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega : i < W.length)]
          simp [W, h1]
        rw [hWi, evalWires_input gs1 (pairInp n m x z) (by rw [hinp]; omega),
          pairInp_getD_x n m x z ⟨i, h1⟩]
        exact ⟨rfl, rfl⟩
      · by_cases h2 : i = n
        · rw [h2]
          have hgt : drInit.getD n (0, 0) = (wF, wT) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            simp only [drInit, Option.getD_some]
            rw [List.getElem_append_right (by simp)]; simp
          rw [hgt, evalWires_input gs5 (pairInp n m x z) (by rw [hinp]; omega),
            evalWires_input gs5 (pairInp n m x z) (by rw [hinp]; omega),
            pairInp_getD_F, pairInp_getD_T, inpVec_getD_m]; exact ⟨rfl, rfl⟩
        · have h3 : i = n + 1 := by omega
          rw [h3]
          have hgt : drInit.getD (n + 1) (0, 0) = (wT, wF) := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            simp only [drInit, Option.getD_some]
            rw [List.getElem_append_right (by simp)]; simp
          rw [hgt, evalWires_input gs5 (pairInp n m x z) (by rw [hinp]; omega),
            evalWires_input gs5 (pairInp n m x z) (by rw [hinp]; omega),
            pairInp_getD_F, pairInp_getD_T, inpVec_getD_m1]; exact ⟨rfl, rfl⟩
    have hsim := hdrOut_ev (pairInp n m x z) (inpVec n x) hinp
      (pairInp_getD_F n m x z) (pairInp_getD_T n m x z) (by rw [inpVec_length, hdrInit_len])
      hagree D.output (by omega)
    rw [← hDeval x]
    exact hsim.2

  have hext16 : Extends gs1 gs6 := hext12.trans (hext23.trans (hext34.trans (hext45.trans hext56)))
  have hnegMid_m : negW.getD (n + (h - 1)) 0 ∈ negW := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; exact List.getElem_mem _
  have hnegMid_W : negW.getD (n + (h - 1)) 0 < M + gs6.length := by
    have := hext56.length_le; have := hnegWW _ hnegMid_m; omega
  obtain ⟨gs6a, midW, hx6_6a, hgs6a, hnc6a, hlen6a, hmidW, hev6a⟩ := mkAnd_ex hgs6 hnegMid_W hnotFx_W
  have hext1_6a : Extends gs1 gs6a := hext16.trans hx6_6a
  have hext5_6a : Extends gs5 gs6a := hext56.trans hx6_6a
  let Llist : List ℕ := List.ofFn fun i : Fin rLen =>
    if i.val + 1 ≤ h then geZ (2 * i.val) else geZ (k + 2 * (i.val - h) + 1)
  let Rlist : List ℕ := List.ofFn fun i : Fin rLen =>
    if i.val + 1 = h then midW else negW.getD (n + i.val) 0
  have hLRlen : Llist.length = Rlist.length := by simp [Llist, Rlist]
  have hLW : ∀ w ∈ Llist, w < M + gs6a.length := by
    intro w hw; simp only [Llist, List.mem_ofFn] at hw
    rcases hw with ⟨i, rfl⟩
    split_ifs
    · have := hext1_6a.length_le; have := hgeZ_W (2 * i.val); omega
    · have := hext1_6a.length_le; have := hgeZ_W (k + 2 * (i.val - h) + 1); omega
  have hRW : ∀ w ∈ Rlist, w < M + gs6a.length := by
    intro w hw; simp only [Rlist, List.mem_ofFn] at hw
    rcases hw with ⟨i, rfl⟩
    split_ifs
    · exact hmidW
    · have hm : negW.getD (n + i.val) 0 ∈ negW := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by dsimp only [rLen] at i; omega)]
        exact List.getElem_mem _
      have := hext5_6a.length_le; have := hnegWW _ hm; omega
  obtain ⟨gs7, outW, hext6a_7, hgs7, hnc7, hlen7, houtW, hev7⟩ :=
    exists_or_and_pairs wF hwF Llist Rlist hLRlen rLen (by simp [Llist]) gs6a hgs6a hLW hRW
  have hnot_tot : notCnt gs7 = b + 1 := by
    have h0 : notCnt ([] : List Gate) = 0 := rfl
    rw [hnc7, hnc6a, hnc6, hnc5, hnc4, hnc3, hnc2, hnc1, h0]; omega
  have hlen_tot : gs7.length ≤ 2 * D.gates.length + K :=
    part3_len_bound hn1 hlen1 hlen2 hlen3 hlen4 hlen5 hlen6 hlen6a hlen7
  refine ⟨⟨gs7, outW⟩, hgs7, houtW, ?_, hnot_tot, hlen_tot⟩
  intro x z
  change wVal gs7 (pairInp n m x z) outW = targetVal k n m f x z
  have hinp := pairInp_length n m x z
  rw [hev7 (pairInp n m x z) hinp (pairInp_getD_F n m x z)]
  have hcz : z.card ≤ m := by
    calc z.card ≤ (Finset.univ : Finset (Fin m)).card := Finset.card_le_univ z
      _ = m := by simp
  have hnegE : ∀ i < rLen,
      wVal gs5 (pairInp n m x z) (negW.getD (n + i) 0) = !(decide (eThr i ≤ z.card)) := by
    intro i hi
    rw [hnegW_spec x z (n + i) (by dsimp only [rLen] at hi; omega)]
    have hWi : W.getD (n + i) 0 = geZ (eThr i) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by dsimp only [rLen] at hi; omega : n + i < W.length)]
      simp only [W, Option.getD_some, List.getElem_ofFn,
        show ¬ (n + i < n) by omega, show n + i < n + rLen by omega, ↓reduceIte, Nat.add_sub_cancel_left]
    rw [hWi, hgeZ_ev x z]
  have hpair_ev : ∀ i < rLen,
      (wVal gs6a (pairInp n m x z) (Llist.getD i 0) = true ∧
       wVal gs6a (pairInp n m x z) (Rlist.getD i 0) = true) ↔
      ((if i + 1 ≤ h then 2 * i ≤ z.card else k + 2 * (i - h) + 1 ≤ z.card) ∧
       z.card < eThr i ∧ (i + 1 = h → f x = false)) := by
    intro i hi
    have hLgt : Llist.getD i 0 = if i + 1 ≤ h then geZ (2 * i) else geZ (k + 2 * (i - h) + 1) := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Llist]; exact hi)]
      simp [Llist]
    have hRgt : Rlist.getD i 0 = if i + 1 = h then midW else negW.getD (n + i) 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [Rlist]; exact hi)]
      simp [Rlist]
    rw [hLgt, hRgt]
    have hL_ev : wVal gs6a (pairInp n m x z) (if i + 1 ≤ h then geZ (2 * i) else geZ (k + 2 * (i - h) + 1)) =
        decide (if i + 1 ≤ h then 2 * i ≤ z.card else k + 2 * (i - h) + 1 ≤ z.card) := by
      split_ifs with hih
      · rw [hext1_6a.wVal_eq (pairInp n m x z) (by rw [hinp]; exact hgeZ_W _), hgeZ_ev x z]
      · rw [hext1_6a.wVal_eq (pairInp n m x z) (by rw [hinp]; exact hgeZ_W _), hgeZ_ev x z]
    rw [hL_ev]
    by_cases hih : i + 1 = h
    · simp only [hih, ↓reduceIte]
      have hieq : i = h - 1 := by omega
      rw [hev6a (pairInp n m x z) hinp,
        hext56.wVal_eq (pairInp n m x z) (by rw [hinp]; exact hnegWW _ hnegMid_m),
        ← hieq, hnegE i hi, hnotFx_ev x z]
      simp only [decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, forall_true_left]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, by omega, h3⟩⟩
    · simp only [hih, ↓reduceIte]
      have hm : negW.getD (n + i) 0 ∈ negW := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by dsimp only [rLen] at hi; omega)]
        exact List.getElem_mem _
      rw [hext5_6a.wVal_eq (pairInp n m x z) (by rw [hinp]; exact hnegWW _ hm), hnegE i hi]
      simp only [decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, IsEmpty.forall_iff, and_true]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1, by omega⟩, fun ⟨h1, h2⟩ => ⟨h1, by omega⟩⟩
  apply Bool.eq_iff_iff.2
  rw [decide_eq_true_eq]
  have hiff_ex : (∃ i < rLen, wVal gs6a (pairInp n m x z) (Llist.getD i 0) = true ∧
      wVal gs6a (pairInp n m x z) (Rlist.getD i 0) = true) ↔
      (∃ i < rLen, (if i + 1 ≤ h then 2 * i ≤ z.card else k + 2 * (i - h) + 1 ≤ z.card) ∧
        z.card < eThr i ∧ (i + 1 = h → f x = false)) := by
    constructor
    · rintro ⟨i, hi, hp⟩; exact ⟨i, hi, (hpair_ev i hi).1 hp⟩
    · rintro ⟨i, hi, hp⟩; exact ⟨i, hi, (hpair_ev i hi).2 hp⟩
  rw [hiff_ex]
  unfold targetVal
  exact part3_target_iff (2 ^ a) z.card (f x) hh_pos hcz

lemma L_lib_1280_core :
    ∀ (a n : Nat),
      let h := 2 ^ a
      let b := a + 1
      let k := 2 * (h - 1)
      let m := 2 * k
      n ≤ 2 * h → ∀ f : Finset (Fin n) → Bool, Monotone f →
        f ∅ = false → f Finset.univ = true →
      let valid := fun (l : Nat) (C : Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (l + 2) C ∧ C.output < l + 2 + C.size
      let source := fun (D : Circuit) =>
        valid n D ∧ ∀ x, D.eval (bitsVec n x ++ [false, true]) = f x
      let target := fun (C : Circuit) =>
        valid (n + m) C ∧ ∀ x z,
          C.eval (bitsVec n x ++ bitsVec m z ++ [false, true]) =
            (if z.card < k then decide (z.card % 2 = 0)
             else if z.card = k then !(f x) else decide (z.card % 2 = 1))
      let K := 96 * (n + m + 2) * (Nat.log2 (n + m + 2) + 2) ^ 2
      (∀ C, target C → b ≤ PEqualNP.NotBracket.notCount C ∧
        (∃ D, source D ∧ D.size ≤ C.size + 1) ∧
        (PEqualNP.NotBracket.notCount C = b →
          ∃ D, source D ∧ PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size)) ∧
      ∀ D, source D →
        (PEqualNP.MetaComplexity.Monotone2 D → ∃ C, target C ∧
          PEqualNP.NotBracket.notCount C = b ∧ C.size ≤ D.size + K) ∧
        ∃ C, target C ∧ PEqualNP.NotBracket.notCount C = b + 1 ∧ C.size ≤ 2 * D.size + K := by
  intro a n h b k m hn f _ hf0 hf1 valid source target K
  constructor
  · intro C ⟨⟨hCf, hCr, hCo⟩, hCe⟩
    obtain ⟨hb, ⟨Dg, hDgOK, hDgO, hDgE, hDgS⟩, hmono⟩ :=
      L_lib_1280_part1 a n f hf0 hf1 C ⟨hCf, hCr⟩ hCo hCe
    refine ⟨by rw [← notCnt_eq_notCount C]; exact hb,
      ⟨Dg, ⟨⟨hDgOK.1, hDgOK.2, hDgO⟩, hDgE⟩, hDgS⟩, ?_⟩
    intro hnc
    obtain ⟨Dm, hDmOK, hDmO, hDmE, hDmM, hDmS⟩ := hmono (by rw [notCnt_eq_notCount C]; exact hnc)
    exact ⟨Dm, ⟨⟨hDmOK.1, hDmOK.2, hDmO⟩, hDmE⟩, hDmM, hDmS⟩
  · intro D ⟨⟨hDf, hDr, hDo⟩, hDe⟩
    constructor
    · intro hDm
      obtain ⟨C, hCOK, hCO, hCE, hCN, hCS⟩ := L_lib_1280_part2 a n f hf0 hf1 D ⟨hDf, hDr⟩ hDo hDe hDm
      exact ⟨C, ⟨⟨hCOK.1, hCOK.2, hCO⟩, hCE⟩, by rw [← notCnt_eq_notCount C]; exact hCN, hCS⟩
    · obtain ⟨C, hCOK, hCO, hCE, hCN, hCS⟩ := L_lib_1280_part3 a n hn f hf0 hf1 D ⟨hDf, hDr⟩ hDo hDe
      exact ⟨C, ⟨⟨hCOK.1, hCOK.2, hCO⟩, hCE⟩, by rw [← notCnt_eq_notCount C]; exact hCN, hCS⟩

end PEqualNP.Outside.L_lib_1280_aux

theorem PEqualNP.Outside.L_lib_1280 :
    letI : ∀ P : Prop, Decidable P := Classical.propDecidable
    ∀ (a n : Nat),
      let h := 2^a
      let b := a+1
      let r := 2*h-1
      let k := 2*(h-1)
      let m := 2*k
      n ≤ 2*h → ∀ f : Finset (Fin n) → Bool, Monotone f →
        f ∅ = false → f Finset.univ = true →
      let bits := fun (l : Nat) (x : Finset (Fin l)) => List.ofFn (fun i : Fin l => decide (i ∈ x))
      let valid := fun (l : Nat) (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        PEqualNP.MetaComplexity.FanInTwo C ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (l+2) C ∧ C.output < l+2+C.size
      let source := fun (D : PEqualNP.CircuitLowerBounds.Circuit) =>
        valid n D ∧ ∀ x, D.eval (bits n x ++ [false,true]) = f x
      let target := fun (C : PEqualNP.CircuitLowerBounds.Circuit) =>
        valid (n+m) C ∧ ∀ x z,
          C.eval (bits n x ++ bits m z ++ [false,true]) =
            (if z.card < k then decide (z.card % 2 = 0)
             else if z.card = k then !(f x) else decide (z.card % 2 = 1))
      let K := 96*(n+m+2)*(Nat.log2 (n+m+2)+2)^2
      (∀ C, target C → b ≤ PEqualNP.NotBracket.notCount C ∧
        (∃ D, source D ∧ D.size ≤ C.size+1) ∧
        (PEqualNP.NotBracket.notCount C = b →
          ∃ D, source D ∧ PEqualNP.MetaComplexity.Monotone2 D ∧ D.size < C.size)) ∧
      ∀ D, source D →
        (PEqualNP.MetaComplexity.Monotone2 D → ∃ C, target C ∧
          PEqualNP.NotBracket.notCount C = b ∧ C.size ≤ D.size + K) ∧
        ∃ C, target C ∧ PEqualNP.NotBracket.notCount C = b+1 ∧ C.size ≤ 2*D.size + K := by
  dsimp only
  intro a n hn f hmono hf0 hf1
  have hdec_mod : ∀ (c d : Nat),
      @decide (c % 2 = d) (Classical.propDecidable _) = decide (c % 2 = d) := by
    intro c d; apply Bool.eq_iff_iff.2; simp
  have hite_lt : ∀ (c k0 : Nat) (u v : Bool),
      @ite Bool (c < k0) (Classical.propDecidable _) u v = if c < k0 then u else v := by
    intro c k0 u v; by_cases h : c < k0 <;> simp [h]
  have hite_eq : ∀ (c k0 : Nat) (u v : Bool),
      @ite Bool (c = k0) (Classical.propDecidable _) u v = if c = k0 then u else v := by
    intro c k0 u v; by_cases h : c = k0 <;> simp [h]
  have hbits : ∀ (l : Nat) (x : Finset (Fin l)),
      List.ofFn (fun i : Fin l => @decide (i ∈ x) (Classical.propDecidable _)) =
        PEqualNP.Outside.L_lib_1280_aux.bitsVec l x := by
    intro l x
    unfold PEqualNP.Outside.L_lib_1280_aux.bitsVec
    apply List.ext_getElem (by simp)
    intro i _ _
    simp only [List.getElem_ofFn]
    apply Bool.eq_iff_iff.2; simp
  have hcore := PEqualNP.Outside.L_lib_1280_aux.L_lib_1280_core a n hn f hmono hf0 hf1
  dsimp only at hcore
  simpa only [hbits, hdec_mod, hite_lt, hite_eq] using hcore
