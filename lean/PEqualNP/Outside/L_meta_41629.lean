import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_41629_aux

def ix {k : Nat} (hk : 0 < k) (i : Nat) : Fin k :=
  ⟨i % k, Nat.mod_lt _ hk⟩

def add {k : Nat} (u v : Fin k → Bool) (i : Fin k) : Bool :=
  xor (u i) (v i)

def mix {k : Nat} (hk : 0 < k) (d : Nat) (x : Fin k → Bool) (i : Fin k) : Bool :=
  xor (x (ix hk (i.val + k - d % k))) (xor (x i) (x (ix hk (i.val + d))))

def rot {k : Nat} (hk : 0 < k) (a : Nat) (x : Fin k → Bool) (i : Fin k) : Bool :=
  x (ix hk (i.val + k - a % k))

def chi {k : Nat} (hk : 0 < k) (r : Fin k → Bool) (i : Fin k) : Bool :=
  xor (r i) (!(r (ix hk (i.val + 1))) && r (ix hk (i.val + 2)))

def row {k : Nat} (hk : 0 < k) (name x : Fin k → Bool) : Fin k → Bool :=
  add (chi hk (mix hk 1 (add name (rot hk 1 x)))) x

lemma ix_val_lt {k : Nat} (hk : 0 < k) {i : Nat} (hi : i < k) :
    ix hk i = ⟨i, hi⟩ := by
  ext
  simp [ix, Nat.mod_eq_of_lt hi]

lemma ix_mod_eq {k : Nat} (hk : 0 < k) (a b : Nat) (h : a % k = b % k) :
    ix hk a = ix hk b := by
  ext
  simp [ix, h]

lemma ix_add_k {k : Nat} (hk : 0 < k) (a : Nat) :
    ix hk (a + k) = ix hk a := by
  apply ix_mod_eq
  rw [Nat.add_mod_right]

lemma ix_val_add {k : Nat} (hk : 0 < k) (a b : Nat) :
    ix hk ((ix hk a).val + b) = ix hk (a + b) := by
  apply ix_mod_eq
  simp [ix, Nat.mod_add_mod]

lemma ix_self_add {k : Nat} (hk : 0 < k) (i : Fin k) (b : Nat) :
    ix hk (i.val + b) = ix hk (i.val + b) := rfl

lemma ix_step_next {k : Nat} (hk : 0 < k) (i : Fin k) :
    ix hk ((ix hk (i.val + 1)).val + 1) = ix hk (i.val + 2) := by
  rw [ix_val_add, Nat.add_assoc]

lemma ix_prev_succ {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (a : Nat) :
    ix hk ((ix hk (a + 1)).val + k - 1 % k) = ix hk a := by
  have hmod1 : 1 % k = 1 := Nat.mod_eq_of_lt hk2
  rw [hmod1]
  apply ix_mod_eq
  simp only [ix]
  rw [Nat.add_sub_assoc (by omega), Nat.mod_add_mod,
    show a + 1 + (k - 1) = a + k by omega, Nat.add_mod_right]

lemma ix_next_prev {k : Nat} (hk : 0 < k) (i : Fin k) :
    ix hk ((ix hk (i.val + k - 1 % k)).val + 1) = i := by
  by_cases hk1 : k = 1
  · subst hk1
    ext
    omega
  · have hk2 : 2 ≤ k := by omega
    have hmod1 : 1 % k = 1 := Nat.mod_eq_of_lt hk2
    rw [hmod1]
    ext
    simp only [ix]
    rw [Nat.mod_add_mod, show i.val + k - 1 + 1 = i.val + k by omega,
      Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

lemma rot1_ix_succ {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (x : Fin k → Bool) (a : Nat) :
    rot hk 1 x (ix hk (a + 1)) = x (ix hk a) := by
  simp only [rot, ix_prev_succ hk hk2 a]

lemma mix1_ix_succ {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (x : Fin k → Bool) (a : Nat) :
    mix hk 1 x (ix hk (a + 1)) =
      xor (x (ix hk a)) (xor (x (ix hk (a + 1))) (x (ix hk (a + 2)))) := by
  simp only [mix, ix_prev_succ hk hk2 a, ix_val_add, Nat.add_assoc]

lemma mix1_rot1_ix_add2 {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k) (x : Fin k → Bool) (a : Nat) :
    mix hk 1 (rot hk 1 x) (ix hk (a + 2)) =
      xor (x (ix hk a)) (xor (x (ix hk (a + 1))) (x (ix hk (a + 2)))) := by
  have h1 := mix1_ix_succ hk hk2 (rot hk 1 x) (a + 1)
  rw [Nat.add_assoc] at h1
  rw [h1, rot1_ix_succ hk hk2 x a, rot1_ix_succ hk hk2 x (a + 1),
    rot1_ix_succ hk hk2 x (a + 2)]

lemma mix1_add {k : Nat} (hk : 0 < k) (d : Nat) (x y : Fin k → Bool) :
    mix hk d (add x y) = add (mix hk d x) (mix hk d y) := by
  funext i
  simp only [mix, add]
  cases x (ix hk (i.val + k - d % k)) <;> cases y (ix hk (i.val + k - d % k)) <;>
    cases x i <;> cases y i <;> cases x (ix hk (i.val + d)) <;>
    cases y (ix hk (i.val + d)) <;> rfl

lemma rot1_add {k : Nat} (hk : 0 < k) (a : Nat) (x y : Fin k → Bool) :
    rot hk a (add x y) = add (rot hk a x) (rot hk a y) := by
  funext i
  rfl

lemma xor_comm_fn {k : Nat} (x y : Fin k → Bool) : add x y = add y x := by
  funext i
  simp only [add, Bool.xor_comm]

lemma xor_assoc_fn {k : Nat} (x y z : Fin k → Bool) :
    add (add x y) z = add x (add y z) := by
  funext i
  simp only [add, Bool.xor_assoc]

lemma xor_zero_left {k : Nat} (x : Fin k → Bool) :
    add (fun _ => false) x = x := by
  funext i
  simp only [add, Bool.false_xor]

lemma xor_zero_right {k : Nat} (x : Fin k → Bool) :
    add x (fun _ => false) = x := by
  funext i
  simp only [add, Bool.xor_false]

lemma xor_cancel_left {k : Nat} (x y : Fin k → Bool) :
    add x (add x y) = y := by
  funext i
  simp only [add]
  cases x i <;> cases y i <;> rfl

lemma xor_self_fn {k : Nat} (x : Fin k → Bool) :
    add x x = fun _ => false := by
  funext i
  simp only [add, Bool.xor_self]

lemma xor_eq_iff {a b c d : Bool} (h : xor a c = xor b d) :
    xor a b = xor c d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma mix1_const {k : Nat} (hk : 0 < k) (b : Bool) :
    mix hk 1 (fun _ => b) = fun _ => b := by
  funext i
  simp only [mix]
  cases b <;> rfl

lemma chi_const {k : Nat} (hk : 0 < k) (b : Bool) :
    chi hk (fun _ => b) = fun _ => b := by
  funext i
  simp only [chi]
  cases b <;> rfl

lemma chi_diff_eq_iff {r0 r1 r2 b0 b1 b2 n0 n1 n2 : Bool}
    (h : xor (xor (xor r0 (!(r1) && r2)) (xor (xor r0 b0) (!(xor r1 b1) && xor r2 b2)))
             (xor (xor (xor r0 n0) (!(xor r1 n1) && xor r2 n2))
                  (xor (xor (xor r0 n0) b0) (!(xor (xor r1 n1) b1) && xor (xor r2 n2) b2))) = false) :
    (n1 && b2) = (n2 && b1) := by
  revert r0 r1 r2 b0 b1 b2 n0 n1 n2
  decide

lemma chi_pair_step_eq {k : Nat} (hk : 0 < k) (N B r Δ : Fin k → Bool)
    (h1 : Δ = add (chi hk r) (chi hk (add r B)))
    (h2 : Δ = add (chi hk (add r N)) (chi hk (add (add r N) B)))
    (p : Fin k) :
    (N (ix hk (p.val + 1)) && B (ix hk (p.val + 2))) =
      (N (ix hk (p.val + 2)) && B (ix hk (p.val + 1))) := by
  have heq : xor (add (chi hk r) (chi hk (add r B)) p)
      (add (chi hk (add r N)) (chi hk (add (add r N) B)) p) = false := by
    rw [← h1, ← h2, Bool.xor_self]
  simp only [add, chi] at heq
  exact chi_diff_eq_iff heq

def xorRange (f : Nat → Bool) : Nat → Bool
  | 0 => false
  | n + 1 => xor (xorRange f n) (f n)

lemma xorRange_mix1_12 {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k)
    (y : Fin k → Bool) (n : Nat) :
    xorRange (fun t =>
      xor (mix hk 1 y (ix hk (3 * t + 1))) (mix hk 1 y (ix hk (3 * t + 2)))) n =
      xor (y (ix hk 0)) (y (ix hk (3 * n))) := by
  induction n with
  | zero =>
    simp [xorRange]
  | succ n ih =>
    simp only [xorRange, ih]
    have h1 := mix1_ix_succ hk hk2 y (3 * n)
    have h2 := mix1_ix_succ hk hk2 y (3 * n + 1)
    rw [Nat.add_assoc] at h2
    rw [h1, h2, show 3 * (n + 1) = 3 * n + 3 by omega, show 3 * n + 1 + 1 = 3 * n + 2 by omega]
    cases y (ix hk 0) <;> cases y (ix hk (3 * n)) <;>
      cases y (ix hk (3 * n + 1)) <;> cases y (ix hk (3 * n + 2)) <;>
      cases y (ix hk (3 * n + 3)) <;> rfl

lemma xorRange_mix1_02 {k : Nat} (hk : 0 < k) (hk2 : 2 ≤ k)
    (z : Fin k → Bool) (n : Nat) :
    xorRange (fun t =>
      xor (mix hk 1 z (ix hk (3 * t))) (mix hk 1 z (ix hk (3 * t + 2)))) n =
      xor (xor (z (ix hk (k - 1))) (z (ix hk (3 * n + k - 1))))
          (xor (z (ix hk 0)) (z (ix hk (3 * n)))) := by
  induction n with
  | zero =>
    rw [show 3 * 0 + k - 1 = k - 1 by omega]
    simp [xorRange]
  | succ n ih =>
    simp only [xorRange, ih]
    have h0 : mix hk 1 z (ix hk (3 * n)) =
        xor (z (ix hk (3 * n + k - 1)))
          (xor (z (ix hk (3 * n))) (z (ix hk (3 * n + 1)))) := by
      have ha : ix hk (3 * n) = ix hk (3 * n + k) := (ix_add_k hk (3 * n)).symm
      rw [ha]
      have hs := mix1_ix_succ hk hk2 z (3 * n + k - 1)
      rw [show 3 * n + k - 1 + 1 = 3 * n + k by omega] at hs
      rw [hs]
      have hb : ix hk (3 * n + k) = ix hk (3 * n) := ix_add_k hk (3 * n)
      have hc : ix hk (3 * n + k - 1 + 2) = ix hk (3 * n + 1) := by
        rw [show 3 * n + k - 1 + 2 = 3 * n + 1 + k by omega, ix_add_k]
      rw [hb, hc]
    have h2 := mix1_ix_succ hk hk2 z (3 * n + 1)
    rw [Nat.add_assoc] at h2
    have hd : ix hk (3 * (n + 1) + k - 1) = ix hk (3 * n + 2) := by
      apply ix_mod_eq
      rw [show 3 * (n + 1) + k - 1 = 3 * n + 2 + k by omega, Nat.add_mod_right]
    have he : 3 * (n + 1) = 3 * n + 3 := by omega
    rw [h0, h2, hd, he, show 3 * n + 1 + 1 = 3 * n + 2 by omega]
    cases z (ix hk (k - 1)) <;> cases z (ix hk (3 * n + k - 1)) <;>
      cases z (ix hk (3 * n + 2)) <;> cases z (ix hk 0) <;>
      cases z (ix hk (3 * n)) <;> cases z (ix hk (3 * n + 3)) <;>
      cases z (ix hk (3 * n + 1)) <;> rfl

lemma xorRange_eq_false_of_all {f : Nat → Bool} {n : Nat}
    (hf : ∀ t, t < n → f t = false) :
    xorRange f n = false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [xorRange]
    rw [ih (fun t ht => hf t (by omega)), hf n (by omega), Bool.xor_false]

lemma k2_mix {k : Nat} (hk : k = 2) (hk0 : 0 < k) :
    let v : Fin k → Bool := fun i => decide (i.val = 1)
    ∀ i : Fin k, mix hk0 1 v i = decide (i.val = 1) := by
  subst hk
  intro v i
  rcases i with ⟨i, hi⟩
  match i with
  | 0 => simp [mix, ix, v]
  | 1 => simp [mix, ix, v]

lemma k2_inj {k : Nat} (hk : k = 2) (hk0 : 0 < k) :
    let v : Fin k → Bool := fun i => decide (i.val = 1)
    ∀ u : Fin k → Bool, Function.Injective (fun x : Fin k → Bool => (row hk0 u x, row hk0 (add u v) x)) := by
  subst hk
  intro v u x x' h
  have h1 : row hk0 u x ⟨0, by omega⟩ = row hk0 u x' ⟨0, by omega⟩ := congrFun (congrArg Prod.fst h) ⟨0, by omega⟩
  have h2 : row hk0 u x ⟨1, by omega⟩ = row hk0 u x' ⟨1, by omega⟩ := congrFun (congrArg Prod.fst h) ⟨1, by omega⟩
  have h3 : row hk0 (add u v) x ⟨0, by omega⟩ = row hk0 (add u v) x' ⟨0, by omega⟩ := congrFun (congrArg Prod.snd h) ⟨0, by omega⟩
  have h4 : row hk0 (add u v) x ⟨1, by omega⟩ = row hk0 (add u v) x' ⟨1, by omega⟩ := congrFun (congrArg Prod.snd h) ⟨1, by omega⟩
  have key : ∀ u0 u1 x0 x1 y0 y1 : Bool,
      let hpos : 0 < 2 := Nat.zero_lt_succ 1
      let ux := fun j : Fin 2 => if j.val = 0 then u0 else u1
      let xx := fun j : Fin 2 => if j.val = 0 then x0 else x1
      let yy := fun j : Fin 2 => if j.val = 0 then y0 else y1
      row hpos ux xx ⟨0, hpos⟩ = row hpos ux yy ⟨0, hpos⟩ →
      row hpos ux xx ⟨1, Nat.lt_succ_self 1⟩ = row hpos ux yy ⟨1, Nat.lt_succ_self 1⟩ →
      row hpos (add ux (fun i : Fin 2 => decide (i.val = 1))) xx ⟨0, hpos⟩ =
        row hpos (add ux (fun i : Fin 2 => decide (i.val = 1))) yy ⟨0, hpos⟩ →
      row hpos (add ux (fun i : Fin 2 => decide (i.val = 1))) xx ⟨1, Nat.lt_succ_self 1⟩ =
        row hpos (add ux (fun i : Fin 2 => decide (i.val = 1))) yy ⟨1, Nat.lt_succ_self 1⟩ →
      x0 = y0 ∧ x1 = y1 := by
    decide
  have hu : u = fun j : Fin 2 => if j.val = 0 then u ⟨0, by omega⟩ else u ⟨1, by omega⟩ := by
    funext j; rcases j with ⟨j, hj⟩; match j with | 0 => rfl | 1 => rfl
  have hx : x = fun j : Fin 2 => if j.val = 0 then x ⟨0, by omega⟩ else x ⟨1, by omega⟩ := by
    funext j; rcases j with ⟨j, hj⟩; match j with | 0 => rfl | 1 => rfl
  have hx' : x' = fun j : Fin 2 => if j.val = 0 then x' ⟨0, by omega⟩ else x' ⟨1, by omega⟩ := by
    funext j; rcases j with ⟨j, hj⟩; match j with | 0 => rfl | 1 => rfl
  rw [hu, hx, hx'] at h1 h2 h3 h4
  obtain ⟨e0, e1⟩ := key (u ⟨0, by omega⟩) (u ⟨1, by omega⟩)
    (x ⟨0, by omega⟩) (x ⟨1, by omega⟩) (x' ⟨0, by omega⟩) (x' ⟨1, by omega⟩) h1 h2 h3 h4
  funext j
  rcases j with ⟨j, hj⟩
  match j with
  | 0 => exact e0
  | 1 => exact e1

lemma k4_mix (k : Nat) (hk4 : 4 ≤ k) (hk : 0 < k) :
    let m := 1 + (k - 1) % 3
    let v : Fin k → Bool := fun i => decide (m + 1 ≤ i.val ∧ (i.val - m) % 3 = 1)
    ∀ i : Fin k, mix hk 1 v i = decide (m ≤ i.val) := by
  intro m v i
  have hm1 : 1 ≤ m := by omega
  have hm3 : m ≤ 3 := by omega
  let q := (k - 1) / 3
  have hq1 : 1 ≤ q := by
    dsimp [q]
    omega
  have hkq : k = 3 * q + m := by
    dsimp [m, q]
    have hdm := Nat.div_add_mod (k - 1) 3
    omega
  have hk2 : 2 ≤ k := by omega
  have hmod1 : 1 % k = 1 := Nat.mod_eq_of_lt hk2
  simp only [mix, hmod1]
  have hv_prev : (i.val + k - 1) % k = if i.val = 0 then k - 1 else i.val - 1 := by
    by_cases hi0 : i.val = 0
    · simp [hi0]
    · simp only [hi0, ite_false]
      rw [show i.val + k - 1 = (i.val - 1) + k by omega, Nat.add_mod_right]
      exact Nat.mod_eq_of_lt (by omega)
  have hv_next : (i.val + 1) % k = if i.val + 1 = k then 0 else i.val + 1 := by
    by_cases hik : i.val + 1 = k
    · simp [hik]
    · simp only [hik, ite_false]
      exact Nat.mod_eq_of_lt (by omega)
  have hi_eq : (ix hk (i.val + k - 1)).val = if i.val = 0 then k - 1 else i.val - 1 := by
    simp only [ix, hv_prev]
  have hn_eq : (ix hk (i.val + 1)).val = if i.val + 1 = k then 0 else i.val + 1 := by
    simp only [ix, hv_next]
  simp only [v, hi_eq, hn_eq]
  by_cases him : i.val < m
  · have hfalse : decide (m ≤ i.val) = false := by
      simp [show ¬(m ≤ i.val) by omega]
    rw [hfalse]
    have h0 : decide (m + 1 ≤ i.val ∧ (i.val - m) % 3 = 1) = false := by
      simp [show ¬(m + 1 ≤ i.val) by omega]
    have hn : decide (m + 1 ≤ (if i.val + 1 = k then 0 else i.val + 1) ∧
        ((if i.val + 1 = k then 0 else i.val + 1) - m) % 3 = 1) = false := by
      split_ifs with h1
      · simp
      · simp; omega
    have hp : decide (m + 1 ≤ (if i.val = 0 then k - 1 else i.val - 1) ∧
        ((if i.val = 0 then k - 1 else i.val - 1) - m) % 3 = 1) = false := by
      split_ifs with h1
      · simp
        intro _
        omega
      · simp
        omega
    rw [hp, h0, hn]
    rfl
  · have htrue : decide (m ≤ i.val) = true := by
      simp [show m ≤ i.val by omega]
    rw [htrue]
    by_cases hieq : i.val = m
    · have hp : decide (m + 1 ≤ (if i.val = 0 then k - 1 else i.val - 1) ∧
          ((if i.val = 0 then k - 1 else i.val - 1) - m) % 3 = 1) = false := by
        split_ifs <;> simp <;> omega
      have h0 : decide (m + 1 ≤ i.val ∧ (i.val - m) % 3 = 1) = false := by
        simp [hieq]
      have hn : decide (m + 1 ≤ (if i.val + 1 = k then 0 else i.val + 1) ∧
          ((if i.val + 1 = k then 0 else i.val + 1) - m) % 3 = 1) = true := by
        split_ifs with h1
        · exfalso; omega
        · simp [hieq]
      rw [hp, h0, hn]
      rfl
    · by_cases hik : i.val + 1 = k
      · have hp : decide (m + 1 ≤ (if i.val = 0 then k - 1 else i.val - 1) ∧
            ((if i.val = 0 then k - 1 else i.val - 1) - m) % 3 = 1) = true := by
          split_ifs with h1
          · exfalso; omega
          · simp; constructor <;> omega
        have h0 : decide (m + 1 ≤ i.val ∧ (i.val - m) % 3 = 1) = false := by
          simp; intro _; omega
        have hn : decide (m + 1 ≤ (if i.val + 1 = k then 0 else i.val + 1) ∧
            ((if i.val + 1 = k then 0 else i.val + 1) - m) % 3 = 1) = false := by
          simp [hik]
        rw [hp, h0, hn]
        rfl
      · have hi0 : i.val ≠ 0 := by omega
        simp only [hi0, hik, ite_false]
        have hp_iff : (m + 1 ≤ i.val - 1 ∧ (i.val - 1 - m) % 3 = 1) ↔
            ((i.val - 1 - m) % 3 = 1) := by
          constructor
          · exact And.right
          · intro hmod
            refine ⟨?_, hmod⟩
            by_contra hlt
            have heq_m : i.val - 1 = m := by omega
            rw [heq_m, Nat.sub_self] at hmod
            cases hmod
        have h0_iff : (m + 1 ≤ i.val ∧ (i.val - m) % 3 = 1) ↔ ((i.val - m) % 3 = 1) := by
          constructor
          · exact And.right
          · intro hmod; exact ⟨by omega, hmod⟩
        have hn_iff : (m + 1 ≤ i.val + 1 ∧ (i.val + 1 - m) % 3 = 1) ↔
            ((i.val + 1 - m) % 3 = 1) := by
          constructor
          · exact And.right
          · intro hmod; exact ⟨by omega, hmod⟩
        have hp_eq : decide (m + 1 ≤ i.val - 1 ∧ (i.val - 1 - m) % 3 = 1) =
            decide ((i.val - 1 - m) % 3 = 1) := by
          rw [decide_eq_decide]; exact hp_iff
        have h0_eq : decide (m + 1 ≤ i.val ∧ (i.val - m) % 3 = 1) =
            decide ((i.val - m) % 3 = 1) := by
          rw [decide_eq_decide]; exact h0_iff
        have hn_eq : decide (m + 1 ≤ i.val + 1 ∧ (i.val + 1 - m) % 3 = 1) =
            decide ((i.val + 1 - m) % 3 = 1) := by
          rw [decide_eq_decide]; exact hn_iff
        rw [hp_eq, h0_eq, hn_eq]
        have hstep1 : i.val - m = (i.val - 1 - m) + 1 := by omega
        have hstep2 : i.val + 1 - m = (i.val - 1 - m) + 2 := by omega
        rw [hstep1, hstep2]
        rcases Nat.mod_lt (i.val - 1 - m) (by omega : 0 < 3) with hmod
        have hcases : (i.val - 1 - m) % 3 = 0 ∨ (i.val - 1 - m) % 3 = 1 ∨
            (i.val - 1 - m) % 3 = 2 := by omega
        rcases hcases with hc | hc | hc
        · have d0 : decide ((i.val - 1 - m) % 3 = 1) = false := by simp [hc]
          have d1 : decide (((i.val - 1 - m) + 1) % 3 = 1) = true := by
            rw [show ((i.val - 1 - m) + 1) % 3 = 1 by omega]; rfl
          have d2 : decide (((i.val - 1 - m) + 2) % 3 = 1) = false := by
            rw [show ((i.val - 1 - m) + 2) % 3 = 2 by omega]; rfl
          rw [d0, d1, d2]; rfl
        · have d0 : decide ((i.val - 1 - m) % 3 = 1) = true := by simp [hc]
          have d1 : decide (((i.val - 1 - m) + 1) % 3 = 1) = false := by
            rw [show ((i.val - 1 - m) + 1) % 3 = 2 by omega]; rfl
          have d2 : decide (((i.val - 1 - m) + 2) % 3 = 1) = false := by
            rw [show ((i.val - 1 - m) + 2) % 3 = 0 by omega]; rfl
          rw [d0, d1, d2]; rfl
        · have d0 : decide ((i.val - 1 - m) % 3 = 1) = false := by simp [hc]
          have d1 : decide (((i.val - 1 - m) + 1) % 3 = 1) = false := by
            rw [show ((i.val - 1 - m) + 1) % 3 = 0 by omega]; rfl
          have d2 : decide (((i.val - 1 - m) + 2) % 3 = 1) = true := by
            rw [show ((i.val - 1 - m) + 2) % 3 = 1 by omega]; rfl
          rw [d0, d1, d2]; rfl

lemma B_eq_const_N {k : Nat} (hk4 : 4 ≤ k) (hk : 0 < k)
    (Δ B : Fin k → Bool)
    (hB : B = mix hk 1 (rot hk 1 Δ))
    (hpair : ∀ p : Fin k,
      let m := 1 + (k - 1) % 3
      let N : Fin k → Bool := fun i => decide (m ≤ i.val)
      (N (ix hk (p.val + 1)) && B (ix hk (p.val + 2))) =
        (N (ix hk (p.val + 2)) && B (ix hk (p.val + 1)))) :
    let m := 1 + (k - 1) % 3
    let N : Fin k → Bool := fun i => decide (m ≤ i.val)
    ∃ c : Bool, ∀ i : Fin k, B i = (c && N i) := by
  intro m N
  have hm1 : 1 ≤ m := by omega
  have hm3 : m ≤ 3 := by omega
  have hkq : k = 3 * ((k - 1) / 3) + m := by
    dsimp [m]
    have hdm := Nat.div_add_mod (k - 1) 3
    omega
  have hq1 : 1 ≤ (k - 1) / 3 := by omega
  have hm_lt : m < k := by omega
  let c := B ⟨m, hm_lt⟩
  refine ⟨c, ?_⟩
  have hstep_ge : ∀ j : Nat, m ≤ j → j + 1 < k →
      B (ix hk j) = B (ix hk (j + 1)) := by
    intro j hmj hj1
    have hp := hpair ⟨j - 1, by omega⟩
    dsimp only at hp
    have h1 : ix hk ((j - 1) + 1) = ix hk j := by rw [Nat.sub_add_cancel (by omega)]
    have h2 : ix hk ((j - 1) + 2) = ix hk (j + 1) := by
      rw [show (j - 1) + 2 = j + 1 by omega]
    rw [h1, h2] at hp
    have hn1 : N (ix hk j) = true := by
      simp [N, ix_val_lt hk (by omega : j < k), hmj]
    have hn2 : N (ix hk (j + 1)) = true := by
      simp [N, ix_val_lt hk hj1, show m ≤ j + 1 by omega]
    dsimp only [N] at hn1 hn2
    rw [hn1, hn2, Bool.true_and, Bool.true_and] at hp
    exact hp.symm
  have hconst_ge : ∀ d : Nat, m + d < k → B (ix hk (m + d)) = c := by
    intro d
    induction d with
    | zero =>
      intro _
      simp [c, ix_val_lt hk hm_lt]
    | succ d ih =>
      intro hd
      rw [← Nat.add_assoc, ← hstep_ge (m + d) (by omega) hd]
      exact ih (by omega)
  have hB0 : B (ix hk 0) = false := by
    have hp := hpair ⟨k - 2, by omega⟩
    dsimp only at hp
    have h1 : ix hk ((k - 2) + 1) = ix hk (k - 1) := by
      rw [show (k - 2) + 1 = k - 1 by omega]
    have h2 : ix hk ((k - 2) + 2) = ix hk 0 := by
      apply ix_mod_eq
      rw [show (k - 2) + 2 = k by omega, Nat.mod_self, Nat.zero_mod]
    rw [h1, h2] at hp
    have hn1 : N (ix hk (k - 1)) = true := by
      simp [N, ix_val_lt hk (by omega : k - 1 < k), show m ≤ k - 1 by omega]
    have hn2 : N (ix hk 0) = false := by
      simp [N, ix_val_lt hk hk, show ¬(m ≤ 0) by omega]
    dsimp only [N] at hn1 hn2
    rw [hn1, hn2, Bool.true_and, Bool.false_and] at hp
    exact hp
  have hBm1 : 2 ≤ m → B (ix hk (m - 1)) = false := by
    intro hm2
    have hp := hpair ⟨m - 2, by omega⟩
    dsimp only at hp
    have h1 : ix hk ((m - 2) + 1) = ix hk (m - 1) := by
      rw [show (m - 2) + 1 = m - 1 by omega]
    have h2 : ix hk ((m - 2) + 2) = ix hk m := by
      rw [show (m - 2) + 2 = m by omega]
    rw [h1, h2] at hp
    have hn1 : N (ix hk (m - 1)) = false := by
      simp [N, ix_val_lt hk (by omega : m - 1 < k), show ¬(m ≤ m - 1) by omega]
    have hn2 : N (ix hk m) = true := by
      simp [N, ix_val_lt hk hm_lt]
    dsimp only [N] at hn1 hn2
    rw [hn1, hn2, Bool.false_and, Bool.true_and] at hp
    exact hp.symm
  have hB1_m3 : m = 3 → B (ix hk 1) = false := by
    intro hm_eq
    have hdiv3 : k = 3 * ((k - 1) / 3 + 1) := by omega
    have htel := xorRange_mix1_12 hk (by omega) (rot hk 1 Δ) ((k - 1) / 3 + 1)
    rw [← hB] at htel
    have hkx : ix hk (3 * ((k - 1) / 3 + 1)) = ix hk 0 := by
      apply ix_mod_eq
      rw [← hdiv3, Nat.mod_self, Nat.zero_mod]
    rw [hkx, Bool.xor_self] at htel
    have hb2 : B (ix hk 2) = false := by
      have := hBm1 (by omega)
      rw [hm_eq] at this
      exact this
    have htail : ∀ t, 1 ≤ t → t < (k - 1) / 3 + 1 →
        xor (B (ix hk (3 * t + 1))) (B (ix hk (3 * t + 2))) = false := by
      intro t ht1 ht2
      have hb1' := hconst_ge (3 * t + 1 - m) (by omega)
      have hb2' := hconst_ge (3 * t + 2 - m) (by omega)
      rw [show m + (3 * t + 1 - m) = 3 * t + 1 by omega] at hb1'
      rw [show m + (3 * t + 2 - m) = 3 * t + 2 by omega] at hb2'
      rw [hb1', hb2', Bool.xor_self]
    have hred : ∀ n, 1 ≤ n → n ≤ (k - 1) / 3 + 1 →
        xorRange (fun t => xor (B (ix hk (3 * t + 1))) (B (ix hk (3 * t + 2)))) n =
          B (ix hk 1) := by
      intro n hn1 hn2
      induction n with
      | zero => omega
      | succ n ih =>
        by_cases hn0 : n = 0
        · subst hn0
          simp [xorRange, hb2]
        · simp only [xorRange]
          rw [ih (by omega) (by omega), htail n (by omega) (by omega), Bool.xor_false]
    rw [hred ((k - 1) / 3 + 1) (by omega) (le_refl _)] at htel
    exact htel
  intro i
  by_cases him : m ≤ i.val
  · have hN : N i = true := by simp [N, him]
    have hBi := hconst_ge (i.val - m) (by omega)
    rw [show m + (i.val - m) = i.val by omega, ix_val_lt hk i.isLt] at hBi
    rw [hN, Bool.and_true, hBi]
  · have hN : N i = false := by simp [N, him]
    rw [hN, Bool.and_false]
    have hi_val : i.val = 0 ∨ (m = 2 ∧ i.val = 1) ∨ (m = 3 ∧ i.val = 1) ∨
        (m = 3 ∧ i.val = 2) := by omega
    rcases hi_val with h0 | ⟨hm2, h1⟩ | ⟨hm3, h1⟩ | ⟨hm3, h2⟩
    · have : i = ix hk 0 := by rw [ix_val_lt hk hk]; ext; exact h0
      rw [this, hB0]
    · have : i = ix hk (m - 1) := by
        rw [ix_val_lt hk (by omega : m - 1 < k)]; ext; dsimp; omega
      rw [this, hBm1 (by omega)]
    · have : i = ix hk 1 := by rw [ix_val_lt hk (by omega : 1 < k)]; ext; exact h1
      rw [this, hB1_m3 hm3]
    · have : i = ix hk (m - 1) := by
        rw [ix_val_lt hk (by omega : m - 1 < k)]; ext; dsimp; omega
      rw [this, hBm1 (by omega)]

lemma xor_true_step {a b c d : Bool}
    (h1 : xor a (xor b c) = true) (h2 : xor b (xor c d) = true) :
    a = d := by
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma chi_diff_pos_true_false {k : Nat} (hk4 : 4 ≤ k) (hk : 0 < k)
    (r Δ : Fin k → Bool)
    (hΔ : Δ = add (chi hk r) (chi hk (add r (fun i => decide (1 + (k - 1) % 3 ≤ i.val))))) :
    let m := 1 + (k - 1) % 3
    (m = 1 → Δ (ix hk (k - 2)) = !(r (ix hk 0)) ∧ Δ (ix hk (k - 1)) = r (ix hk 0)) ∧
    (2 ≤ m → Δ (ix hk (k - 1)) = true) ∧
    (m = 3 →
      Δ (ix hk 0) = false ∧
      Δ (ix hk 1) = !(r (ix hk 2)) ∧
      Δ (ix hk 2) = xor (r (ix hk 3)) (r (ix hk 4)) ∧
      Δ (ix hk (k - 2)) = !(r (ix hk 0)) ∧
      (∀ i : Nat, 3 ≤ i → i + 2 < k →
        Δ (ix hk i) = !(xor (r (ix hk (i + 1))) (r (ix hk (i + 2)))))) := by
  intro m
  let N : Fin k → Bool := fun i => decide (m ≤ i.val)
  have hk2 : 2 ≤ k := by omega
  have hm1 : 1 ≤ m := by omega
  have hm3 : m ≤ 3 := by omega
  have hkm1_N : N (ix hk (k - 1)) = true := by
    simp [N, ix_val_lt hk (by omega : k - 1 < k), show m ≤ k - 1 by omega]
  have hkm2_N : N (ix hk (k - 2)) = true := by
    simp [N, ix_val_lt hk (by omega : k - 2 < k), show m ≤ k - 2 by omega]
  have h0_N : N (ix hk 0) = false := by
    simp [N, ix_val_lt hk hk, show ¬(m ≤ 0) by omega]
  have h1_step_km2 : ix hk ((ix hk (k - 2)).val + 1) = ix hk (k - 1) := by
    rw [ix_val_add, show k - 2 + 1 = k - 1 by omega]
  have h2_step_km2 : ix hk ((ix hk (k - 2)).val + 2) = ix hk 0 := by
    rw [ix_val_add]; apply ix_mod_eq; rw [show k - 2 + 2 = k by omega, Nat.mod_self, Nat.zero_mod]
  have h1_step_km1 : ix hk ((ix hk (k - 1)).val + 1) = ix hk 0 := by
    rw [ix_val_add]; apply ix_mod_eq; rw [show k - 1 + 1 = k by omega, Nat.mod_self, Nat.zero_mod]
  have h2_step_km1 : ix hk ((ix hk (k - 1)).val + 2) = ix hk 1 := by
    rw [ix_val_add]; apply ix_mod_eq; rw [show k - 1 + 2 = 1 + k by omega, Nat.add_mod_right]
  have eval_at : ∀ p : Fin k, Δ p =
      xor (xor (r p) (!(r (ix hk (p.val + 1))) && r (ix hk (p.val + 2))))
          (xor (xor (r p) (N p))
               (!(xor (r (ix hk (p.val + 1))) (N (ix hk (p.val + 1)))) &&
                 xor (r (ix hk (p.val + 2))) (N (ix hk (p.val + 2))))) := by
    intro p
    rw [hΔ]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro hm_eq
    have h1_N : N (ix hk 1) = true := by
      simp [N, ix_val_lt hk (by omega : 1 < k), hm_eq]
    have ekm2 := eval_at (ix hk (k - 2))
    rw [h1_step_km2, h2_step_km2, hkm2_N, hkm1_N, h0_N] at ekm2
    have ekm1 := eval_at (ix hk (k - 1))
    rw [h1_step_km1, h2_step_km1, hkm1_N, h0_N, h1_N] at ekm1
    refine ⟨?_, ?_⟩
    · rw [ekm2]
      cases r (ix hk (k - 2)) <;> cases r (ix hk (k - 1)) <;> cases r (ix hk 0) <;> rfl
    · rw [ekm1]
      cases r (ix hk (k - 1)) <;> cases r (ix hk 0) <;> cases r (ix hk 1) <;> rfl
  · intro hm2
    have h1_N : N (ix hk 1) = false := by
      simp [N, ix_val_lt hk (by omega : 1 < k), show ¬(m ≤ 1) by omega]
    have ekm1 := eval_at (ix hk (k - 1))
    rw [h1_step_km1, h2_step_km1, hkm1_N, h0_N, h1_N] at ekm1
    rw [ekm1]
    cases r (ix hk (k - 1)) <;> cases r (ix hk 0) <;> cases r (ix hk 1) <;> rfl
  · intro hm3_eq
    have hkq : k = 3 * ((k - 1) / 3) + 3 := by
      dsimp [m] at hm3_eq ⊢
      have hdm := Nat.div_add_mod (k - 1) 3
      omega
    have hk6 : 6 ≤ k := by
      have : 1 ≤ (k - 1) / 3 := by omega
      omega
    have h1_N : N (ix hk 1) = false := by
      simp [N, ix_val_lt hk (by omega : 1 < k), hm3_eq]
    have h2_N : N (ix hk 2) = false := by
      simp [N, ix_val_lt hk (by omega : 2 < k), hm3_eq]
    have h3_N : N (ix hk 3) = true := by
      simp [N, ix_val_lt hk (by omega : 3 < k), hm3_eq]
    have h4_N : N (ix hk 4) = true := by
      simp [N, ix_val_lt hk (by omega : 4 < k), hm3_eq]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · have e0 := eval_at (ix hk 0)
      rw [ix_val_add, ix_val_add, Nat.zero_add, Nat.zero_add, h0_N, h1_N, h2_N] at e0
      rw [e0]
      cases r (ix hk 0) <;> cases r (ix hk 1) <;> cases r (ix hk 2) <;> rfl
    · have e1 := eval_at (ix hk 1)
      rw [ix_val_add, ix_val_add, show 1 + 1 = 2 by rfl, show 1 + 2 = 3 by rfl,
        h1_N, h2_N, h3_N] at e1
      rw [e1]
      cases r (ix hk 1) <;> cases r (ix hk 2) <;> cases r (ix hk 3) <;> rfl
    · have e2 := eval_at (ix hk 2)
      rw [ix_val_add, ix_val_add, show 2 + 1 = 3 by rfl, show 2 + 2 = 4 by rfl,
        h2_N, h3_N, h4_N] at e2
      rw [e2]
      cases r (ix hk 2) <;> cases r (ix hk 3) <;> cases r (ix hk 4) <;> rfl
    · have ekm2 := eval_at (ix hk (k - 2))
      rw [h1_step_km2, h2_step_km2, hkm2_N, hkm1_N, h0_N] at ekm2
      rw [ekm2]
      cases r (ix hk (k - 2)) <;> cases r (ix hk (k - 1)) <;> cases r (ix hk 0) <;> rfl
    · intro i hi3 hik
      have hi0_N : N (ix hk i) = true := by
        simp [N, ix_val_lt hk (by omega : i < k), hm3_eq, hi3]
      have hi1_N : N (ix hk (i + 1)) = true := by
        simp [N, ix_val_lt hk (by omega : i + 1 < k), hm3_eq, show 3 ≤ i + 1 by omega]
      have hi2_N : N (ix hk (i + 2)) = true := by
        simp [N, ix_val_lt hk hik, hm3_eq, show 3 ≤ i + 2 by omega]
      have ei := eval_at (ix hk i)
      rw [ix_val_add, ix_val_add, hi0_N, hi1_N, hi2_N] at ei
      rw [ei]
      cases r (ix hk i) <;> cases r (ix hk (i + 1)) <;> cases r (ix hk (i + 2)) <;> rfl

lemma period3_step {k : Nat} (hk4 : 4 ≤ k) (hk : 0 < k)
    (Δ : Fin k → Bool)
    (hmix : mix hk 1 (rot hk 1 Δ) = fun i => decide (1 + (k - 1) % 3 ≤ i.val)) :
    let m := 1 + (k - 1) % 3
    let q := (k - 1) / 3
    ∀ n, n + 2 ≤ 3 * q →
      Δ (ix hk (m + k - 2 + n)) = Δ (ix hk (m + k - 2 + (n + 3))) := by
  intro m q n hn
  have hm1 : 1 ≤ m := by omega
  have hm3 : m ≤ 3 := by omega
  have hkq : k = 3 * q + m := by
    dsimp [m, q]
    have hdm := Nat.div_add_mod (k - 1) 3
    omega
  have hk2 : 2 ≤ k := by omega
  have hN_fn : ∀ p, 2 ≤ p → p ≤ 3 * q + 1 →
      decide (m ≤ (ix hk (m + k - 2 + p)).val) = true := by
    intro p hp2 hpq
    have hmod : ix hk (m + k - 2 + p) = ix hk (m + p - 2) := by
      apply ix_mod_eq
      rw [show m + k - 2 + p = (m + p - 2) + k by omega, Nat.add_mod_right]
    rw [hmod, ix_val_lt hk (by omega : m + p - 2 < k)]
    simp [show m ≤ m + p - 2 by omega]
  have e1 := congrFun hmix (ix hk (m + k - 2 + n + 2))
  have e2 := congrFun hmix (ix hk (m + k - 2 + n + 3))
  have h1_rhs := hN_fn (n + 2) (by omega) (by omega)
  have h2_rhs := hN_fn (n + 3) (by omega) (by omega)
  rw [show m + k - 2 + (n + 2) = m + k - 2 + n + 2 by omega] at h1_rhs
  rw [show m + k - 2 + (n + 3) = m + k - 2 + n + 3 by omega] at h2_rhs
  rw [h1_rhs] at e1
  rw [h2_rhs] at e2
  rw [mix1_rot1_ix_add2 hk hk2 Δ (m + k - 2 + n)] at e1
  have hadd2 : m + k - 2 + n + 3 = (m + k - 2 + n + 1) + 2 := by omega
  rw [hadd2, mix1_rot1_ix_add2 hk hk2 Δ (m + k - 2 + n + 1)] at e2
  rw [show m + k - 2 + n + 1 + 1 = m + k - 2 + n + 2 by omega,
    show m + k - 2 + n + 1 + 2 = m + k - 2 + (n + 3) by omega] at e2
  exact xor_true_step e1 e2

lemma period3_multi {k : Nat} (hk4 : 4 ≤ k) (hk : 0 < k)
    (Δ : Fin k → Bool)
    (hmix : mix hk 1 (rot hk 1 Δ) = fun i => decide (1 + (k - 1) % 3 ≤ i.val)) :
    let m := 1 + (k - 1) % 3
    let q := (k - 1) / 3
    ∀ s t, s + 3 * t ≤ 3 * q + 1 →
      Δ (ix hk (m + k - 2 + s)) = Δ (ix hk (m + k - 2 + (s + 3 * t))) := by
  intro m q s t
  induction t with
  | zero =>
    intro _
    simp
  | succ t ih =>
    intro hle
    have h1 := ih (by omega)
    have h2 := period3_step hk4 hk Δ hmix (s + 3 * t) (by omega)
    rw [show s + 3 * (t + 1) = s + 3 * t + 3 by omega]
    exact h1.trans h2

lemma B_eq_N_impossible {k : Nat} (hk4 : 4 ≤ k) (hk : 0 < k)
    (u x : Fin k → Bool)
    (Δ : Fin k → Bool)
    (hmix_delta : mix hk 1 (rot hk 1 Δ) = fun i => decide (1 + (k - 1) % 3 ≤ i.val))
    (hchi_delta : Δ = add (chi hk (mix hk 1 (add u (rot hk 1 x))))
        (chi hk (add (mix hk 1 (add u (rot hk 1 x)))
          (fun i => decide (1 + (k - 1) % 3 ≤ i.val))))) :
    False := by
  let m := 1 + (k - 1) % 3
  let q := (k - 1) / 3
  let z := add u (rot hk 1 x)
  let r := mix hk 1 z
  have hm1 : 1 ≤ m := by omega
  have hm3 : m ≤ 3 := by omega
  have hkq : k = 3 * q + m := by
    dsimp [m, q]
    have hdm := Nat.div_add_mod (k - 1) 3
    omega
  have hq1 : 1 ≤ q := by omega
  have hk2 : 2 ≤ k := by omega
  have hper := period3_multi hk4 hk Δ hmix_delta
  have h1 := hper 0 q (by omega)
  have h2 := hper 1 q (by omega)
  have hend0 : ix hk (m + k - 2 + (0 + 3 * q)) = ix hk (k - 2) := by
    apply ix_mod_eq
    rw [show m + k - 2 + (0 + 3 * q) = (k - 2) + k by omega, Nat.add_mod_right]
  have hstart1 : ix hk (m + k - 2 + 1) = ix hk (m - 1) := by
    apply ix_mod_eq
    rw [show m + k - 2 + 1 = (m - 1) + k by omega, Nat.add_mod_right]
  have hchi := chi_diff_pos_true_false hk4 hk r Δ hchi_delta
  rcases hchi with ⟨hc1, hc2, hc3⟩
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 3 := by omega
  rcases hm_cases with hm_eq | hm_eq | hm_eq
  · have hstart_m1 : ix hk (m + k - 2 + 0) = ix hk (k - 1) := by
      apply ix_mod_eq
      rw [hm_eq, show 1 + k - 2 + 0 = k - 1 by omega]
    have eq_km : Δ (ix hk (k - 1)) = Δ (ix hk (k - 2)) := by
      rw [← hstart_m1, h1, hend0]
    obtain ⟨ea, eb⟩ := hc1 hm_eq
    rw [ea, eb] at eq_km
    cases h0v : r (ix hk 0) <;> rw [h0v] at eq_km <;> cases eq_km
  · have hstart_m2 : ix hk (m + k - 2 + 0) = ix hk 0 := by
      apply ix_mod_eq
      rw [hm_eq, show 2 + k - 2 + 0 = k by omega, Nat.mod_self, Nat.zero_mod]
    have hstart1_m2 : ix hk (m + k - 2 + 1) = ix hk 1 := by
      rw [hstart1, hm_eq]
    have hend1_m2 : ix hk (m + k - 2 + (1 + 3 * q)) = ix hk (k - 1) := by
      apply ix_mod_eq
      rw [show m + k - 2 + (1 + 3 * q) = (k - 1) + k by omega, Nat.add_mod_right]
    have eq0 : Δ (ix hk 0) = Δ (ix hk (k - 2)) := by
      rw [← hstart_m2, h1, hend0]
    have eq1 : Δ (ix hk 1) = Δ (ix hk (k - 1)) := by
      rw [← hstart1_m2, h2, hend1_m2]
    have emix0 := congrFun hmix_delta (ix hk 0)
    have h0_ix : ix hk 0 = ix hk (k - 2 + 2) := by
      apply ix_mod_eq
      rw [show k - 2 + 2 = k by omega, Nat.mod_self, Nat.zero_mod]
    rw [h0_ix, mix1_rot1_ix_add2 hk hk2 Δ (k - 2)] at emix0
    have ha : ix hk (k - 2 + 1) = ix hk (k - 1) := by
      rw [show k - 2 + 1 = k - 1 by omega]
    have hN0 : decide (1 + (k - 1) % 3 ≤ (ix hk 0).val) = false := by
      simp [ix_val_lt hk hk]
    rw [← h0_ix, hN0, ha, ← eq0] at emix0
    have htrue := hc2 (by omega)
    rw [htrue] at emix0
    cases hd0v : Δ (ix hk 0) <;> rw [hd0v] at emix0 <;> cases emix0
  · have hstart0_m3 : ix hk (m + k - 2 + 0) = ix hk 1 := by
      apply ix_mod_eq
      rw [hm_eq, show 3 + k - 2 + 0 = 1 + k by omega, Nat.add_mod_right]
    have hstart1_m3 : ix hk (m + k - 2 + 1) = ix hk 2 := by
      rw [hstart1, hm_eq]
    have hend1_m3 : ix hk (m + k - 2 + (1 + 3 * q)) = ix hk (k - 1) := by
      apply ix_mod_eq
      rw [show m + k - 2 + (1 + 3 * q) = (k - 1) + k by omega, Nat.add_mod_right]
    obtain ⟨hd0, hd1, hd2, hdkm2, hdi_ge⟩ := hc3 hm_eq
    have eq1 : Δ (ix hk 1) = Δ (ix hk (k - 2)) := by
      rw [← hstart0_m3, h1, hend0]
    have eq2 : Δ (ix hk 2) = Δ (ix hk (k - 1)) := by
      rw [← hstart1_m3, h2, hend1_m3]
    have hkm1_N : decide (m ≤ (ix hk (k - 1)).val) = true := by
      simp [ix_val_lt hk (by omega : k - 1 < k), show m ≤ k - 1 by omega]
    have emix0 := congrFun hmix_delta (ix hk 0)
    have h0_ix : ix hk 0 = ix hk (k - 2 + 2) := by
      apply ix_mod_eq
      rw [show k - 2 + 2 = k by omega, Nat.mod_self, Nat.zero_mod]
    rw [h0_ix, mix1_rot1_ix_add2 hk hk2 Δ (k - 2)] at emix0
    have ha : ix hk (k - 2 + 1) = ix hk (k - 1) := by
      rw [show k - 2 + 1 = k - 1 by omega]
    have hN0 : decide (1 + (k - 1) % 3 ≤ (ix hk 0).val) = false := by
      simp [ix_val_lt hk hk]
    rw [← h0_ix, hN0, ha, hd0, Bool.xor_false] at emix0
    have hkm1_true := hc2 (by omega)
    rw [hkm1_true] at emix0
    have hkm2_true : Δ (ix hk (k - 2)) = true := by
      cases hval : Δ (ix hk (k - 2))
      · rw [hval] at emix0; cases emix0
      · rfl
    have h1_true : Δ (ix hk 1) = true := eq1.trans hkm2_true
    have h2_true : Δ (ix hk 2) = true := eq2.trans hkm1_true
    have hr2 : r (ix hk 2) = false := by
      rw [h1_true] at hd1
      cases hr : r (ix hk 2)
      · rfl
      · rw [hr] at hd1; cases hd1
    have hr0 : r (ix hk 0) = false := by
      rw [hkm2_true] at hdkm2
      cases hr : r (ix hk 0)
      · rfl
      · rw [hr] at hdkm2; cases hdkm2
    have hr34 : r (ix hk 3) = !(r (ix hk 4)) := by
      rw [h2_true] at hd2
      cases h3 : r (ix hk 3) <;> cases h4 : r (ix hk 4) <;>
        rw [h3, h4] at hd2 <;> first | rfl | cases hd2
    have hk6 : 6 ≤ k := by omega
    have hΔ_ge1 : ∀ j : Nat, 1 ≤ j → j < k → Δ (ix hk j) = true := by
      intro j hj1 hjk
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        by_cases hj12 : j = 1 ∨ j = 2
        · rcases hj12 with rfl | rfl <;> assumption
        · have hj3 : 3 ≤ j := by omega
          have emixj := congrFun hmix_delta (ix hk j)
          have hj_ix : ix hk j = ix hk (j - 2 + 2) := by
            rw [show j - 2 + 2 = j by omega]
          rw [hj_ix, mix1_rot1_ix_add2 hk hk2 Δ (j - 2)] at emixj
          have hNj : decide (1 + (k - 1) % 3 ≤ (ix hk j).val) = true := by
            rw [ix_val_lt hk hjk]
            change decide (m ≤ j) = true
            rw [hm_eq]
            exact decide_eq_true hj3
          rw [← hj_ix, hNj, show j - 2 + 1 = j - 1 by omega,
            ih (j - 2) (by omega) (by omega) (by omega),
            ih (j - 1) (by omega) (by omega) (by omega)] at emixj
          cases hval : Δ (ix hk j)
          · rw [hval] at emixj; cases emixj
          · rfl
    have hri_ge : ∀ i : Nat, 3 ≤ i → i + 2 < k →
        r (ix hk (i + 1)) = r (ix hk (i + 2)) := by
      intro i hi3 hik
      have hde := hdi_ge i hi3 hik
      rw [hΔ_ge1 i (by omega) (by omega)] at hde
      have hbool : ∀ a b : Bool, true = !(xor a b) → a = b := by decide
      exact hbool _ _ hde
    have hr_const : ∀ j : Nat, 4 ≤ j → j < k → r (ix hk j) = r (ix hk 4) := by
      intro j hj4 hjk
      induction j with
      | zero => omega
      | succ j ih =>
        by_cases hj4' : j + 1 = 4
        · rw [hj4']
        · have hj3 : 3 ≤ j - 1 := by omega
          have hstep := hri_ge (j - 1) hj3 (by omega)
          rw [show j - 1 + 1 = j by omega, show j - 1 + 2 = j + 1 by omega] at hstep
          rw [← hstep]
          exact ih (by omega) (by omega)
    have htel := xorRange_mix1_02 hk hk2 z (q + 1)
    have hq_eq : 3 * (q + 1) = k := by omega
    have hkx1 : ix hk (3 * (q + 1) + k - 1) = ix hk (k - 1) := by
      apply ix_mod_eq
      rw [hq_eq, show k + k - 1 = (k - 1) + k by omega, Nat.add_mod_right]
    have hkx2 : ix hk (3 * (q + 1)) = ix hk 0 := by
      apply ix_mod_eq
      rw [hq_eq, Nat.mod_self, Nat.zero_mod]
    rw [hkx1, hkx2, Bool.xor_self, Bool.xor_self, Bool.false_xor] at htel
    have hr_t0 : xor (r (ix hk 0)) (r (ix hk 2)) = false := by
      rw [hr0, hr2]; rfl
    have hr_t1 : xor (r (ix hk 3)) (r (ix hk 5)) = true := by
      rw [hr34, hr_const 5 (by omega) (by omega)]
      cases r (ix hk 4) <;> rfl
    have hr_tail : ∀ t, 2 ≤ t → t < q + 1 →
        xor (r (ix hk (3 * t))) (r (ix hk (3 * t + 2))) = false := by
      intro t ht2 htq
      rw [hr_const (3 * t) (by omega) (by omega),
        hr_const (3 * t + 2) (by omega) (by omega), Bool.xor_self]
    have hsum : ∀ n, 2 ≤ n → n ≤ q + 1 →
        xorRange (fun t => xor (r (ix hk (3 * t))) (r (ix hk (3 * t + 2)))) n = true := by
      intro n hn2 hnq
      induction n with
      | zero => omega
      | succ n ih =>
        by_cases hn1 : n = 1
        · subst hn1
          simp [xorRange, hr_t0, hr_t1]
        · simp only [xorRange]
          rw [ih (by omega) (by omega), hr_tail n (by omega) (by omega), Bool.xor_false]
    have htrue_sum := hsum (q + 1) (by omega) (le_refl _)
    change xorRange (fun t => xor (r (ix hk (3 * t))) (r (ix hk (3 * t + 2)))) (q + 1) =
      false at htel
    rw [htrue_sum] at htel
    cases htel

end PEqualNP.Outside.L_meta_41629_aux

namespace PEqualNP.Outside.L_meta_41629_aux

lemma k4_inj (k : Nat) (hk4 : 4 ≤ k) (hk : 0 < k) :
    let m := 1 + (k - 1) % 3
    let v : Fin k → Bool := fun i => decide (m + 1 ≤ i.val ∧ (i.val - m) % 3 = 1)
    ∀ u : Fin k → Bool,
      Function.Injective (fun x : Fin k → Bool => (row hk u x, row hk (add u v) x)) := by
  intro m v u x x' h
  have hux : row hk u x = row hk u x' := congrArg Prod.fst h
  have huvx : row hk (add u v) x = row hk (add u v) x' := congrArg Prod.snd h
  let Δ := add x x'
  let B := mix hk 1 (rot hk 1 Δ)
  let r := mix hk 1 (add u (rot hk 1 x))
  let N : Fin k → Bool := fun i => decide (m ≤ i.val)
  have hmv : mix hk 1 v = N := by
    funext i
    exact k4_mix k hk4 hk i
  have hx' : x' = add x Δ := (xor_cancel_left x x').symm
  have hrot_x' : add u (rot hk 1 x') = add (add u (rot hk 1 x)) (rot hk 1 Δ) := by
    conv_lhs => rw [hx', rot1_add]
    rw [xor_assoc_fn]
  have hmix_ux' : mix hk 1 (add u (rot hk 1 x')) = add r B := by
    rw [hrot_x', mix1_add]
  have huv_x : add (add u v) (rot hk 1 x) = add (add u (rot hk 1 x)) v := by
    rw [xor_assoc_fn, xor_comm_fn v (rot hk 1 x), ← xor_assoc_fn]
  have hmix_uvx : mix hk 1 (add (add u v) (rot hk 1 x)) = add r N := by
    rw [huv_x, mix1_add, hmv]
  have huv_x' : add (add u v) (rot hk 1 x') =
      add (add (add u (rot hk 1 x)) v) (rot hk 1 Δ) := by
    rw [xor_assoc_fn, xor_comm_fn v (rot hk 1 x'), ← xor_assoc_fn, hrot_x']
    rw [xor_assoc_fn, xor_comm_fn (rot hk 1 Δ) v, ← xor_assoc_fn]
  have hmix_uvx' : mix hk 1 (add (add u v) (rot hk 1 x')) = add (add r N) B := by
    rw [huv_x', mix1_add, mix1_add, hmv]
  have hΔ1 : Δ = add (chi hk r) (chi hk (add r B)) := by
    funext i
    have hi := congrFun hux i
    simp only [row, add] at hi
    rw [hmix_ux'] at hi
    exact (xor_eq_iff hi).symm
  have hΔ2 : Δ = add (chi hk (add r N)) (chi hk (add (add r N) B)) := by
    funext i
    have hi := congrFun huvx i
    simp only [row, add] at hi
    rw [hmix_uvx, hmix_uvx'] at hi
    exact (xor_eq_iff hi).symm
  have hpair : ∀ p : Fin k,
      (N (ix hk (p.val + 1)) && B (ix hk (p.val + 2))) =
        (N (ix hk (p.val + 2)) && B (ix hk (p.val + 1))) :=
    fun p => chi_pair_step_eq hk N B r Δ hΔ1 hΔ2 p
  obtain ⟨c, hc⟩ := B_eq_const_N hk4 hk Δ B rfl hpair
  cases c
  · have hB0 : B = fun _ => false := by
      funext i
      rw [hc i, Bool.false_and]
    have hΔ0 : Δ = fun _ => false := by
      rw [hΔ1, hB0, xor_zero_right, xor_self_fn]
    rw [hx', hΔ0, xor_zero_right]
  · have hBN : B = N := by
      funext i
      rw [hc i, Bool.true_and]
    have hmix_delta : mix hk 1 (rot hk 1 Δ) = fun i => decide (1 + (k - 1) % 3 ≤ i.val) :=
      hBN
    have hchi_delta : Δ = add (chi hk r) (chi hk (add r (fun i => decide (1 + (k - 1) % 3 ≤ i.val)))) := by
      have hBN' : B = fun i => decide (1 + (k - 1) % 3 ≤ i.val) := hBN
      rw [← hBN']
      exact hΔ1
    exact False.elim (B_eq_N_impossible hk4 hk u x Δ hmix_delta hchi_delta)

lemma part_B (k : Nat) (hk : 0 < k) (hk24 : k = 2 ∨ 4 ≤ k) :
    let m := 1 + (k - 1) % 3
    ∃ v : Fin k → Bool,
      (∀ i : Fin k, mix hk 1 v i = (if k = 2 then decide (i.val = 1) else decide (m ≤ i.val))) ∧
      ∀ u : Fin k → Bool,
        Function.Injective (fun x : Fin k → Bool => (row hk u x, row hk (add u v) x)) := by
  intro m
  rcases hk24 with rfl | hk4
  · refine ⟨fun i => decide (i.val = 1), ?_, k2_inj rfl hk⟩
    intro i
    simp only [ite_true]
    exact k2_mix rfl hk i
  · have hne2 : k ≠ 2 := by omega
    refine ⟨fun i => decide (m + 1 ≤ i.val ∧ (i.val - m) % 3 = 1), ?_, k4_inj k hk4 hk⟩
    intro i
    simp only [hne2, ite_false]
    exact k4_mix k hk4 hk i

lemma k1_no_inj {k q : Nat} (hk1 : k = 1) (hk : 0 < k) (names : Fin q → Fin k → Bool)
    (hinj : Function.Injective (fun x : Fin k → Bool => fun j : Fin q => row hk (names j) x)) :
    False := by
  subst hk1
  have eq_fn : (fun j : Fin q => row hk (names j) (fun _ => false)) =
      (fun j : Fin q => row hk (names j) (fun _ => true)) := by
    funext j i
    rcases i with ⟨i, hi⟩
    have hi0 : i = 0 := by omega
    subst hi0
    have key : ∀ b : Bool,
        let hpos : 0 < 1 := Nat.zero_lt_succ 0
        let n := fun _ : Fin 1 => b
        row hpos n (fun _ => false) ⟨0, hpos⟩ = row hpos n (fun _ => true) ⟨0, hpos⟩ := by
      decide
    have hn : names j = fun _ => names j ⟨0, hk⟩ := by
      funext a; rcases a with ⟨a, ha⟩; have ha0 : a = 0 := by omega
      congr 1; exact Fin.ext ha0
    rw [hn]
    exact key (names j ⟨0, hk⟩)
  have hfx := hinj eq_fn
  have hval := congrFun hfx ⟨0, hk⟩
  cases hval

lemma k3_no_inj {k q : Nat} (hk3 : k = 3) (hk : 0 < k) (names : Fin q → Fin k → Bool)
    (hinj : Function.Injective (fun x : Fin k → Bool => fun j : Fin q => row hk (names j) x)) :
    False := by
  subst hk3
  have eq_fn : (fun j : Fin q => row hk (names j) (fun _ => false)) =
      (fun j : Fin q => row hk (names j) (fun _ => true)) := by
    funext j i
    have key : ∀ n0 n1 n2 : Bool,
        let hpos : 0 < 3 := Nat.zero_lt_succ 2
        let n : Fin 3 → Bool := fun a =>
          if a.val = 0 then n0 else if a.val = 1 then n1 else n2
        ∀ a : Fin 3, row hpos n (fun _ => false) a = row hpos n (fun _ => true) a := by
      decide
    have hn : names j = fun a : Fin 3 =>
        if a.val = 0 then names j ⟨0, by omega⟩
        else if a.val = 1 then names j ⟨1, by omega⟩
        else names j ⟨2, by omega⟩ := by
      funext a; rcases a with ⟨a, ha⟩
      match a with
      | 0 => rfl
      | 1 => rfl
      | 2 => rfl
    rw [hn]
    exact key (names j ⟨0, by omega⟩) (names j ⟨1, by omega⟩) (names j ⟨2, by omega⟩) i
  have hfx := hinj eq_fn
  have hval := congrFun hfx ⟨0, hk⟩
  cases hval

lemma q_le1_no_inj {k q : Nat} (hk : 0 < k) (hq : q < 2) (names : Fin q → Fin k → Bool)
    (hinj : Function.Injective (fun x : Fin k → Bool => fun j : Fin q => row hk (names j) x)) :
    False := by
  by_cases hq0 : q = 0
  · subst hq0
    have heq : (fun j : Fin 0 => row hk (names j) (fun _ => false)) =
        (fun j : Fin 0 => row hk (names j) (fun _ => true)) := by
      funext j
      exact Fin.elim0 j
    have hfx := hinj heq
    have hval := congrFun hfx ⟨0, hk⟩
    cases hval
  · have hq1 : q = 1 := by omega
    subst hq1
    let name := names ⟨0, by omega⟩
    let x0 : Fin k → Bool := fun i => name (ix hk (i.val + 1))
    let x1 : Fin k → Bool := fun i => !(x0 i)
    have hrot0 : rot hk 1 x0 = name := by
      funext i
      simp only [rot, x0, ix_next_prev hk i]
    have hadd0 : add name (rot hk 1 x0) = fun _ => false := by
      rw [hrot0, xor_self_fn]
    have hrow0 : row hk name x0 = x0 := by
      rw [row, hadd0, mix1_const, chi_const, xor_zero_left]
    have hx1_eq : x1 = add x0 (fun _ => true) := by
      funext i
      simp only [x1, add]
      cases x0 i <;> rfl
    have hrot1 : rot hk 1 x1 = add name (fun _ => true) := by
      rw [hx1_eq, rot1_add, hrot0]
      rfl
    have hadd1 : add name (rot hk 1 x1) = fun _ => true := by
      rw [hrot1, xor_cancel_left]
    have hrow1 : row hk name x1 = x0 := by
      rw [row, hadd1, mix1_const, chi_const]
      funext i
      simp only [add, x1]
      cases x0 i <;> rfl
    have heq : (fun j : Fin 1 => row hk (names j) x0) =
        (fun j : Fin 1 => row hk (names j) x1) := by
      funext j
      have hj : j = ⟨0, by omega⟩ := Fin.eq_zero j
      rw [hj]
      change row hk name x0 = row hk name x1
      rw [hrow0, hrow1]
    have hfx := hinj heq
    have hval := congrFun hfx ⟨0, hk⟩
    have hx01 : x1 ⟨0, hk⟩ = !(x0 ⟨0, hk⟩) := rfl
    rw [← hval] at hx01
    cases h0 : x0 ⟨0, hk⟩ <;> rw [h0] at hx01 <;> cases hx01

lemma part_A (k : Nat) (hk : 0 < k) (q : Nat) :
    (∃ names : Fin q → Fin k → Bool,
      Function.Injective (fun x : Fin k → Bool => fun j : Fin q => row hk (names j) x)) ↔
    k ≠ 1 ∧ k ≠ 3 ∧ 2 ≤ q := by
  constructor
  · rintro ⟨names, hinj⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hk1; exact k1_no_inj hk1 hk names hinj
    · intro hk3; exact k3_no_inj hk3 hk names hinj
    · by_contra hlt
      exact q_le1_no_inj hk (by omega) names hinj
  · rintro ⟨hk1, hk3, hq2⟩
    have hk24 : k = 2 ∨ 4 ≤ k := by omega
    obtain ⟨v, _, hv_inj⟩ := part_B k hk hk24
    let u : Fin k → Bool := fun _ => false
    let names : Fin q → Fin k → Bool := fun j => if j.val = 0 then u else v
    refine ⟨names, ?_⟩
    intro x x' h
    have h0 := congrFun h ⟨0, by omega⟩
    have h1 := congrFun h ⟨1, by omega⟩
    dsimp only at h0 h1
    have hn0 : names ⟨0, by omega⟩ = u := by simp [names]
    have hn1 : names ⟨1, by omega⟩ = add u v := by
      simp [names, u, xor_zero_left]
    rw [hn0] at h0
    rw [hn1] at h1
    exact hv_inj u (Prod.ext h0 h1)

end PEqualNP.Outside.L_meta_41629_aux

theorem PEqualNP.Outside.L_meta_41629 :
  ∀ (k : Nat) (hk : 0 < k),
    let W := Fin k → Bool
    let ix := fun (i : Nat) => (⟨i % k, Nat.mod_lt _ hk⟩ : Fin k)
    let add := fun (u v : W) (i : Fin k) => xor (u i) (v i)
    let mix := fun (d : Nat) (x : W) (i : Fin k) =>
      xor (x (ix (i.val+k-d % k))) (xor (x i) (x (ix (i.val+d))))
    let rot := fun (a : Nat) (x : W) (i : Fin k) => x (ix (i.val+k-a % k))
    let chi := fun (r : W) (i : Fin k) => xor (r i) (!(r (ix (i.val+1))) && r (ix (i.val+2)))
    let row := fun (name x : W) => add (chi (mix 1 (add name (rot 1 x)))) x
    let m := 1 + (k-1) % 3
    (∀ q : Nat, (∃ names : Fin q → W, Function.Injective (fun x : W => fun j : Fin q => row (names j) x)) ↔
      k ≠ 1 ∧ k ≠ 3 ∧ 2 ≤ q) ∧
    ((k = 2 ∨ 4 ≤ k) → ∃ v : W,
      (∀ i : Fin k, mix 1 v i = (if k = 2 then decide (i.val = 1) else decide (m ≤ i.val))) ∧
      ∀ u : W, Function.Injective (fun x : W => (row u x, row (add u v) x))) := by
  intro k hk
  exact ⟨fun q => PEqualNP.Outside.L_meta_41629_aux.part_A k hk q,
    fun hk24 => PEqualNP.Outside.L_meta_41629_aux.part_B k hk hk24⟩
