import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_47707_aux
namespace CoreSigned

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

set_option maxRecDepth 100000 in
theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

set_option maxRecDepth 100000 in
theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

set_option maxRecDepth 100000 in
theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

set_option maxRecDepth 100000 in
theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

end CoreSigned

namespace SignedProjection
variable {α β : Type} [DecidableEq α] [DecidableEq β] [Zero β]

def avail (pin : α → β) (S : Finset α) := (S.image pin).erase 0
def lost (pin : α → β) (S : Finset α) := (S.filter fun x => pin x = 0).card

theorem avail_mem (pin : α → β) {S : Finset α} {x : β} :
    x ∈ avail pin S ↔ x ≠ 0 ∧ ∃ a ∈ S, pin a = x := by simp [avail]

theorem avail_mono (pin : α → β) {S T : Finset α} (h : S ⊆ T) : avail pin S ⊆ avail pin T := by
  intro y hy
  obtain ⟨hn,x,hx,rfl⟩ := (avail_mem pin).mp hy
  exact (avail_mem pin).mpr ⟨hn,x,h hx,rfl⟩

theorem avail_cases (pin : α → β) {S : Finset α} {c : α} {x : β} (h : x ∈ avail pin (insert c S)) :
    x = pin c ∨ x ∈ avail pin S := by
  obtain ⟨hn,y,hy,rfl⟩ := (avail_mem pin).mp h
  rcases Finset.mem_insert.mp hy with rfl|hy
  · exact Or.inl rfl
  · exact Or.inr ((avail_mem pin).mpr ⟨hn,y,hy,rfl⟩)

theorem lost_insert (pin : α → β) (c : α) (S : Finset α) :
    lost pin (insert c S) = lost pin S + (if pin c = 0 ∧ c ∉ S then 1 else 0) := by
  by_cases mem : c ∈ S
  · rw [Finset.insert_eq_of_mem mem,ite_eq_right (fun q => q.2 mem),Nat.add_zero]
  · by_cases h : pin c = 0
    · rw [ite_eq_left ⟨h,mem⟩]
      unfold lost
      rw [Finset.filter_insert,ite_eq_left h,Finset.card_insert_of_notMem]
      exact fun q => mem (Finset.mem_filter.mp q).1
    · rw [ite_eq_right (fun q => h q.1),Nat.add_zero]
      unfold lost
      rw [Finset.filter_insert,ite_eq_right h]

theorem projected (pin : α → β) (ops : α → α → Finset α) (ops2 : β → β → Finset β) (goal : α)
    (hgoal : pin goal ≠ 0)
    (maps : ∀ {a b c}, c ∈ ops a b → pin c ∈ ops2 (pin a) (pin b))
    (idA : ∀ {a b c}, c ∈ ops2 a b → a = 0 → c = 0 ∨ c = b)
    (idB : ∀ {a b c}, c ∈ ops2 a b → b = 0 → c = 0 ∨ c = a)
    (idS : ∀ {a b c}, c ∈ ops2 a b → a = b → c = 0 ∨ c = b)
    {k : Nat} {S : Finset α} (h : CoreSigned.live ops goal k S) :
    ∃ j, j + lost pin S ≤ k ∧ ∃ T ⊆ avail pin S, CoreSigned.live ops2 (pin goal) j T := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at h
    subst S
    exact ⟨0,by simp [lost,hgoal],{(pin goal)},by simp [avail,hgoal],rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a,_,b,_,ne,c,op,fresh,U,rfl,tail⟩
    · obtain ⟨j,hj,ws,sub,hws⟩ := ih skip
      exact ⟨j,by omega,ws,sub,hws⟩
    let prev := insert a (insert b U)
    have cnew : c ∉ U := fun h => fresh (by simp [h])
    have repr := maps op
    obtain ⟨j,limit,T,sub,path⟩ := ih tail
    have both (ha : pin a = 0) (hb : pin b = 0) : pin c = 0 := by
      exact (idA repr ha).elim id (fun e => e.trans hb)
    have skipcost : lost pin prev ≤ lost pin (insert c U) + 1 := by
      simp only [prev,lost_insert]
      split_ifs <;> grind
    have liftU : avail pin U ⊆ avail pin prev := avail_mono pin (by intro u hu; simp [prev,hu])
    by_cases useful : pin c ∈ T ∧ pin c ∉ avail pin prev
    · have nz := ((avail_mem pin).mp (sub useful.1)).1
      have df (v : α) (hv : v ∈ prev) : pin c ≠ pin v := by
        intro e
        exact useful.2 ((avail_mem pin).mpr ⟨nz,v,hv,e.symm⟩)
      have da := df a (by simp [prev])
      have db := df b (by simp [prev])
      have ha : pin a ≠ 0 := fun e => (idA repr e).elim nz db
      have hb : pin b ≠ 0 := fun e => (idB repr e).elim nz da
      have distinct : pin a ≠ pin b := fun e => (idS repr e).elim nz db
      have vcost : lost pin prev ≤ lost pin (insert c U) := by
        simp only [prev,lost_insert]
        split_ifs <;> grind
      let V := T.erase (pin c)
      have old (v : β) (hv : v ∈ V) : v ∈ avail pin U :=
        (avail_cases pin (sub (Finset.mem_erase.mp hv).2)).resolve_left (Finset.mem_erase.mp hv).1
      let B := insert (pin a) (insert (pin b) V)
      refine ⟨j+1,by change j+1+lost pin prev ≤ k+1; omega,B,?_,Or.inr ?_⟩
      · intro v hv
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨ha,a,by simp,rfl⟩
        rcases Finset.mem_insert.mp hv with rfl|hv
        · exact (avail_mem pin).mpr ⟨hb,b,by simp,rfl⟩
        exact liftU (old _ hv)
      · refine ⟨pin a,by simp [B],pin b,by simp [B],distinct,pin c,?_,?_,V,rfl,?_⟩
        · exact repr
        · simp [B,V,da,db]
        · rwa [show insert (pin c) V = T from Finset.insert_erase useful.1]
    · refine ⟨j,by change j+lost pin prev ≤ k+1; omega,T,?_,path⟩
      intro v hv
      rcases avail_cases pin (sub hv) with rfl|old
      · by_contra miss
        exact useful ⟨hv,miss⟩
      · exact liftU old

end SignedProjection

namespace SignedProjection
variable {n : Nat}

def signedOps (a b : BitVec n) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a].toFinset

theorem zero_left {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = 0) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

theorem zero_right {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : b = 0) : c = 0 ∨ c = a := by
  subst b
  simpa [signedOps,or_comm] using h

theorem equal_inputs {a b c : BitVec n} (h : c ∈ signedOps a b) (eq : a = b) : c = 0 ∨ c = b := by
  subst a
  simpa [signedOps,or_comm] using h

def signedPin (mask : BitVec n) (base : Fin n) (x : BitVec n) : BitVec n :=
  (if x[base.val] then ~~~x else x) &&& mask

theorem masked_ops (m : BitVec n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    c &&& m ∈ signedOps (a &&& m) (b &&& m) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl
  · left; ext i h; simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  · right;left; ext i h; simp only [BitVec.getElem_or,BitVec.getElem_and]; cases a[i] <;> cases b[i] <;> simp
  · right;right;left; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide
  · right;right;right; ext i h
    simp only [BitVec.getElem_and,BitVec.getElem_not]
    cases a[i] <;> cases b[i] <;> cases m[i] <;> decide

def polarity (b : Bool) (x : BitVec n) := if b then ~~~x else x

theorem polarity_ops (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    polarity (c[i.val]) c ∈ signedOps (polarity (a[i.val]) a) (polarity (b[i.val]) b) := by
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at *
  rcases h with rfl|rfl|rfl|rfl <;>
    simp only [BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not] <;>
    cases a[i.val] <;> cases b[i.val] <;>
    simp [polarity,BitVec.not_and,BitVec.not_or,BitVec.and_comm,BitVec.or_comm]

theorem signedPin_ops (m : BitVec n) (i : Fin n) {a b c : BitVec n} (h : c ∈ signedOps a b) :
    signedPin m i c ∈ signedOps (signedPin m i a) (signedPin m i b) :=
  masked_ops m (polarity_ops i h)

theorem live_build {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}
    {k : Nat} {S V : Finset α} (h : CoreSigned.live ops goal k S) (sub : S ⊆ V) :
    CoreSigned.build ops goal k V := by
  induction k generalizing S V with
  | zero => change S = {goal} at h; subst S; exact sub (Finset.mem_singleton_self _)
  | succ k ih =>
    rcases h with skip|⟨a,ha,b,hb,ne,c,opc,_,rest,eq,tail⟩
    · exact Or.inl (ih skip sub)
    · refine Or.inr ⟨a,sub ha,b,sub hb,ne,c,opc,ih tail ?_⟩
      intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hr
      · simp
      · exact Finset.mem_insert_of_mem (sub (eq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hr)))

end SignedProjection

namespace SignedProjection
variable {α : Type} [DecidableEq α]

def generated (ops : α → α → Finset α) (stock : Finset α) : List (α × α × α) → Finset α → Prop
  | [], result => stock = result
  | (a,b,w) :: rest, result =>
    a ∈ stock ∧ b ∈ stock ∧ a ≠ b ∧ w ∈ ops a b ∧ generated ops (insert w stock) rest result

theorem extend_generated {ops : α → α → Finset α} {goal : α} {stock result : Finset α}
    {recipe : List (α × α × α)} {k : ℕ}
    (h : generated ops stock recipe result) (tail : CoreSigned.build ops goal k result) :
    CoreSigned.build ops goal (k + recipe.length) stock := by
  induction recipe generalizing stock with
  | nil => change stock = result at h; simpa [h] using tail
  | cons step rest ih =>
    obtain ⟨a,b,w⟩ := step
    rcases h with ⟨ha,hb,hn,ho,hrest⟩
    change CoreSigned.build ops goal (k+rest.length+1) stock
    exact Or.inr ⟨a,ha,b,hb,hn,w,ho,ih hrest⟩

theorem pad_build {ops : α → α → Finset α} {goal : α} {S : Finset α} {a b : Nat}
    (le : a ≤ b) (ha : CoreSigned.build ops goal a S) : CoreSigned.build ops goal b S := by
  induction le with
  | refl => exact ha
  | step _ ih => exact Or.inl ih

end SignedProjection

namespace SignedProjection
variable {n : Nat}

theorem exclude_cut (m : BitVec n) (i : Fin n) (goal : BitVec n) (k cap : ℕ)
    (S A U : Finset (BitVec n)) (recipes : List (BitVec n × BitVec n × BitVec n))
    (nonzero : signedPin m i goal ≠ 0)
    (bound : ¬ CoreSigned.build signedOps (signedPin m i goal) cap A)
    (regen : generated signedOps A recipes U) (sub : avail (signedPin m i) S ⊆ U)
    (budget : recipes.length + k ≤ cap + lost (signedPin m i) S) :
    ¬ CoreSigned.live signedOps goal k S := by
  intro h
  obtain ⟨j, hj, T, ht, path⟩ := projected (signedPin m i) signedOps signedOps goal nonzero
    (signedPin_ops m i) zero_left zero_right equal_inputs h
  have localRun := live_build path (ht.trans sub)
  exact bound (pad_build (by omega) (extend_generated regen localRun))

end SignedProjection

namespace SignedProjection
open CoreSigned (live build first_live live_card pairs pick_two live_separates)

abbrev Word := BitVec 64
def signedList (a b : Word) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]
theorem ops_swap (a b : Word) : signedOps a b = signedOps b a := by
  ext z
  simp only [signedOps, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto
def keepChoices (a b : Word) (r : List Word) : List (List Word) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List Word} {a b : Word} {needed : Finset Word}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {goal : Word} {ws : List Word} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : Word) : List Word → List Word
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List Word) := ws.foldr insertW []

theorem insertW_perm (v : Word) (ws : List Word) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List Word) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

theorem perm_set {u v : List Word} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

def children (k : Nat) (ws : List Word) : List (List Word) :=
  (pairs ws).flatMap fun (a,b,r) => (signedList a b).flatMap fun z =>
    if z ∈ ws then [] else
      (keepChoices a b r).filterMap fun kept =>
        if kept.length ≤ k then some (ordered (z :: kept)) else none

theorem zero_prune {goal : Word} (nz : goal ≠ 0) {k : Nat} {S : Finset Word}
    (h : live signedOps goal k S) : ∃ j ≤ k, ∃ T ⊆ S.erase 0, live signedOps goal j T := by
  obtain ⟨j,le,T,sub,path⟩ := projected id signedOps signedOps goal nz (fun q => q)
    zero_left zero_right equal_inputs h
  refine ⟨j,by omega,T,?_,path⟩
  simpa [avail] using sub

theorem step_no (goal : Word) (n : Nat) (ws : List Word) (hn : ws.Nodup)
    (done_ : ws ≠ [goal])
    (children_ : ∀ qs ∈ children n ws, ¬ live signedOps goal n qs.toFinset)
    : ¬ live signedOps goal (n+1) ws.toFinset := by
  intro h
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · exact done_ (singleton_list hn done)
  obtain ⟨r,hm,hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
  have go {a b : Word} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
      (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ signedOps a b) : False := by
    obtain ⟨kept,hkeep,hnk,hfin⟩ := recover_kept hp hn hset
    have hznew : z ∉ kept := by
      intro hu
      apply hout
      rw [hset]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ List.mem_toFinset.mpr hu))
    have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
    have hraw : live signedOps goal n (z :: kept).toFinset := by simpa [hfin] using tail
    have hc := live_card hraw
    rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
    have hzws : z ∉ ws := by simpa using hout
    have hp' := ordered_perm (z :: kept)
    have mem : ordered (z :: kept) ∈ children n ws := by
      apply List.mem_flatMap.mpr
      refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
      simpa only [hzws,ite_false] using
        (List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ n by omega]⟩ :
          ordered (z::kept) ∈ ((keepChoices a b r).filterMap fun kept =>
            if kept.length ≤ n then some (ordered (z :: kept)) else none))
    exact children_ _ mem ((perm_set hp').symm ▸ hraw)
  rcases hm with direct|swap
  · exact go hp direct hs hz
  · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)
end SignedProjection

namespace SignedProjection
abbrev V64 := BitVec 64

def bitAt (w : V64) (n : Nat) := w.getLsbD n
def mismatch (g : V64) (ws : List V64) (p q : Nat) :=
  (bitAt g p != bitAt g q) && ws.all (fun w => bitAt w p == bitAt w q)

theorem mismatch_sound {g : V64} {ws : List V64} {p q : Nat} (pp : p < 64) (qq : q < 64)
    (cert : mismatch g ws p q = true) (k : ℕ) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  intro h
  have parts := Bool.and_eq_true_iff.mp cert
  let D : V64 → Prop := fun w => bitAt w p ≠ bitAt w q
  have dg : D g := by simpa [D] using parts.1
  have hop (a b : V64) (z : V64) (hz : z ∈ signedOps a b) (dz : D z) : D a ∨ D b := by
    by_contra! fail
    apply dz
    obtain ⟨ea,eb⟩ := fail
    simp only [D, not_not] at ea eb
    change bitAt a p = bitAt a q at ea
    change bitAt b p = bitAt b q at eb
    simp only [signedOps, List.mem_toFinset,List.mem_cons, List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl <;>
      simpa only [bitAt, BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not,
        pp,qq,decide_true, Bool.true_and, show a.getLsbD p = a.getLsbD q from ea,
        show b.getLsbD p = b.getLsbD q from eb]
  obtain ⟨x,hx,dx⟩ := CoreSigned.live_separates D dg hop h
  exact dx (beq_iff_eq.mp (List.all_eq_true.mp parts.2 x (List.mem_toFinset.mp hx)))

end SignedProjection

namespace SignedProjection
abbrev View := Word × Fin 64 × Word × List Word × Nat × (Nat → Nat)
abbrev Node := Nat × Nat × List Word × (Nat → Nat)
def vm (v : View) := v.1
def va (v : View) := v.2.1
def vg (v : View) := v.2.2.1
def vs (v : View) := v.2.2.2.1
def vk (v : View) := v.2.2.2.2.1
def vh (v : View) := v.2.2.2.2.2
def nv (a : Node) := a.1
def nk (a : Node) := a.2.1
def ns (a : Node) := a.2.2.1
def nh (a : Node) := a.2.2.2

def recipeRun : Nat → Nat → List Word → Option (List (Word × Word × Word) × List Word)
  | 0, code, ws => if code = 1 then some ([],ws) else none
  | fuel+1, code, ws => if code = 1 then some ([],ws) else
    let i := code % 16
    let j := (code / 16) % 16
    let o := (code / 256) % 4
    match ws[i]?, ws[j]? with
    | some a, some b => if a = b then none else
      let w := (signedList a b).getD o 0
      match recipeRun fuel (code / 1024) (ws++[w]) with
      | some (rs,ws') => some ((a,b,w)::rs,ws')
      | none => none
    | _,_ => none

theorem recipeRun_sound (fuel code : Nat) (ws : List Word) {rs out}
    (h : recipeRun fuel code ws = some (rs,out)) :
    generated signedOps ws.toFinset rs out.toFinset := by
  induction fuel generalizing code ws rs out with
  | zero =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    · contradiction
  | succ k ih =>
    simp only [recipeRun] at h
    split at h
    · cases h; rfl
    split at h <;> try contradiction
    rename_i a b ha hb
    split at h <;> try contradiction
    rename_i ne
    split at h <;> try contradiction
    rename_i tail end_ ht
    cases h
    set r := (code / 256) % 4
    let w := (signedList a b).getD r 0
    change a ∈ ws.toFinset ∧ b ∈ ws.toFinset ∧ a ≠ b ∧ w ∈ signedOps a b ∧ _
    refine ⟨List.mem_toFinset.mpr (List.mem_of_getElem? ha),
      List.mem_toFinset.mpr (List.mem_of_getElem? hb),ne,?_,?_⟩
    · have hr : r < 4 := Nat.mod_lt _ (by decide)
      change w ∈ (signedList a b).toFinset
      simp only [List.mem_toFinset]
      have hr' : r < (signedList a b).length := by simpa [signedList] using hr
      simpa [w, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hr'] using
        (List.getElem_mem (l := signedList a b) (i := r) hr')
    · have eq : (ws++[w]).toFinset = insert w ws.toFinset := by
        ext x
        simp [or_comm]
      rw [← eq]
      exact ih _ _ ht

def ViewOK (v : View) := ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset

def cutOK (v : View) (g : Word) (k : Nat) (ws : List Word) (recipe : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 recipe (vs v) with
    | none => false
    | some (rs,out) =>
      decide (avail p ws.toFinset ⊆ out.toFinset) &&
      decide (rs.length+k ≤ vk v + lost p ws.toFinset)

theorem cutOK_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {recipe : Nat}
    (hv : ViewOK v) (hc : cutOK v g k ws recipe = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [cutOK] at hc
  split at hc <;> try contradiction
  rename_i ok
  split at hc <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp hc
  have good : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using ok
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs good.2
    (good.1 ▸ hv) (recipeRun_sound _ _ _ hr) (of_decide_eq_true parts.1)
    (of_decide_eq_true parts.2)

end SignedProjection
namespace SignedProjection

def quickCut (v : View) (g : Word) (k : Nat) (ws : List Word) (receipt : Nat) : Bool :=
  let p := signedPin (vm v) (va v)
  if p g != vg v || p g == 0 then false else
    match recipeRun 12 receipt (vs v) with
    | none => false
    | some (rs,out) =>
      decide ws.Nodup &&
      ws.all (fun w => p w == 0 || out.contains (p w)) &&
      decide (rs.length+k ≤ vk v + ws.countP (fun w => p w = 0))

theorem quickCut_sound {v : View} {g : Word} {k : Nat} {ws : List Word} {receipt : Nat}
    (hv : ViewOK v) (ok : quickCut v g k ws receipt = true) :
    ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [quickCut] at ok
  split at ok <;> try contradiction
  rename_i good
  split at ok <;> try contradiction
  rename_i rs out hr
  have parts := Bool.and_eq_true_iff.mp ok
  have pp := Bool.and_eq_true_iff.mp parts.1
  have nd := of_decide_eq_true pp.1
  have gg : signedPin (vm v) (va v) g = vg v ∧ signedPin (vm v) (va v) g ≠ 0 := by
    simpa using good
  apply exclude_cut (vm v) (va v) g k (vk v) ws.toFinset (vs v).toFinset out.toFinset rs gg.2
    (gg.1 ▸ hv) (recipeRun_sound _ _ _ hr)
  · intro x hx
    obtain ⟨ne,w,hw,rfl⟩ := (avail_mem _).mp hx
    have has := List.all_eq_true.mp pp.2 w (List.mem_toFinset.mp hw)
    simp only [Bool.or_eq_true,beq_iff_eq,List.contains_iff_mem] at has
    exact List.mem_toFinset.mpr (has.resolve_left ne)
  · unfold lost
    rw [List.Nodup.card_eq_countP nd]
    exact of_decide_eq_true parts.2

end SignedProjection

namespace SignedProjection.QFast
abbrev Table (α : Type) := Nat × (Nat → Option α)
def get {α : Type} (t : Table α) (i : Nat) : Option α := if i < t.1 then t.2 i else none

def checkHint (views : Table View) (nodes : Table Node) (vID : Nat) (g : Word)
    (k : Nat) (ws : List Word) (hint : Nat) : Bool :=
  let val := hint/4
  match hint % 4 with
  | 0 => mismatch g ws (val % 64) ((val/64)%64)
  | 1 => match (get nodes val) with
    | some a => (nv a == vID) && (nk a == k) && (ns a == ws)
    | none => false
  | 2 =>
    let j := val % 1024
    if j < vID then
      match (get views j) with
      | some v => quickCut v g k ws (val/1024)
      | none => false
    else false
  | _ => (k == 0 && ws.toFinset != {g}) || decide (k+1 < ws.toFinset.card)

theorem checkHint_sound {views : Table View} {nodes : Table Node} {vID : Nat} {g : Word}
    {k : Nat} {ws : List Word} {h : Nat}
    (known : ∀ i < vID, ∀ v, (get views i) = some v → ViewOK v)
    (closed : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps g k (ns a).toFinset)
    (ok : checkHint views nodes vID g k ws h = true) : ¬ CoreSigned.live signedOps g k ws.toFinset := by
  simp only [checkHint] at ok
  split at ok
  · exact mismatch_sound (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide)) ok k
  · split at ok <;> try contradiction
    rename_i a ha
    simp only [Bool.and_eq_true,beq_iff_eq] at ok
    exact ok.2 ▸ closed _ a ha ok.1.1 ok.1.2
  · split at ok <;> try contradiction
    rename_i lt
    split at ok <;> try contradiction
    rename_i v hv
    exact quickCut_sound (known _ lt _ hv) ok
  · simp only [Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,bne_iff_ne,decide_eq_true_eq] at ok
    intro h
    rcases ok with ⟨rfl,ne⟩|wide
    · exact ne h
    · exact (Nat.not_lt_of_ge (CoreSigned.live_card h)) wide

def scanFrom {α : Type} (f : Nat → α → Bool) : Nat → List α → Bool
  | _, [] => true
  | i, x::xs => f i x && scanFrom f (i+1) xs

theorem scanFrom_sound {α : Type} (f : Nat → α → Bool) {i : Nat} {xs : List α}
    (ok : scanFrom f i xs = true) {x : α} (hx : x ∈ xs) : ∃ j, f j x = true := by
  induction xs generalizing i with
  | nil => simp at hx
  | cons a xs ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    rcases List.mem_cons.mp hx with rfl|hm
    · exact ⟨_,parts.1⟩
    · exact ih parts.2 hm

def evalNode (views : Table View) (nodes : Table Node) (a : Node) : Bool :=
  match (get views (nv a)) with
  | none => false
  | some v => decide (ns a).Nodup && (ns a != [vg v]) &&
    match nk a with
    | 0 => true
    | k+1 => scanFrom (fun i ws => checkHint views nodes (nv a) (vg v) k ws (nh a i)) 0
               (children k (ns a))

def evalRoot (views : Table View) (nodes : Table Node) (i : Nat) (v : View) : Bool :=
  scanFrom (fun q ws => checkHint views nodes i (vg v) (vk v) ws (vh v q)) 0 (vs v).sublists

theorem view_from_earlier (views : Table View) (nodes : Table Node) (vID : Nat) (v : View)
    (hv : (get views vID) = some v)
    (earlier : ∀ i < vID, ∀ w, (get views i) = some w → ViewOK w)
    (hroots : evalRoot views nodes vID v = true)
    (hnodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true) :
    ViewOK v := by
  have closed (k : Nat) : ∀ (i : Nat) (a : Node), (get nodes i) = some a → nv a = vID → nk a = k →
      ¬ CoreSigned.live signedOps (vg v) k (ns a).toFinset := by
    induction k with
    | zero =>
      intro i a found owner fuel h
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_true,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      exact ok.2 (singleton_list ok.1 h)
    | succ k ih =>
      intro i a found owner fuel
      have ok := hnodes i a found
      simp only [evalNode,owner,hv,fuel,Bool.and_eq_true,decide_eq_true_eq,bne_iff_ne] at ok
      apply step_no _ _ _ ok.1.1 ok.1.2
      intro ws hm
      obtain ⟨j,good⟩ := scanFrom_sound _ ok.2 hm
      exact checkHint_sound earlier ih good
  intro build_
  classical
  obtain ⟨S, sub, path⟩ := CoreSigned.compress build_
  let ws := (vs v).filter (· ∈ S)
  have eq : ws.toFinset = S := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (sub hw)
  obtain ⟨q,hq⟩ := scanFrom_sound _ hroots (show ws ∈ (vs v).sublists from
    List.mem_sublists.mpr (List.filter_sublist ..))
  exact checkHint_sound earlier (closed _) hq (eq.symm ▸ path)

theorem whole_sound (views : Table View) (nodes : Table Node)
    (allRoots : ∀ (i : Nat) (v : View), (get views i) = some v → evalRoot views nodes i v = true)
    (allNodes : ∀ (i : Nat) (a : Node), (get nodes i) = some a → evalNode views nodes a = true)
    (i : Nat) (v : View) (hv : (get views i) = some v) : ViewOK v := by
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih => exact view_from_earlier views nodes i v hv ih (allRoots i v hv) allNodes

def checkRootAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get views i) with
  | some v => evalRoot views nodes i v
  | none => true

def checkNodeAt (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match (get nodes i) with
  | some a => evalNode views nodes a
  | none => true

def passBlock (check : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => passBlock check start n && check (start+n)

theorem block_at (check : Nat → Bool) {s n i} (ok : passBlock check s n = true)
    (lo : s ≤ i) (hi : i < s+n) : check i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    have parts := Bool.and_eq_true_iff.mp ok
    by_cases lt : i < s+n
    · exact ih parts.1 lt
    · have eq : i = s+n := by omega
      exact eq ▸ parts.2

theorem merge_blocks {c : Nat → Bool} {s a b : Nat} (x : passBlock c s a = true)
    (y : passBlock c (s+a) b = true) : passBlock c s (a+b) = true := by
  induction b with
  | zero => simpa using x
  | succ b ih =>
    have parts := Bool.and_eq_true_iff.mp y
    change passBlock c s (a+b) && c (s+(a+b)) = true
    exact Bool.and_eq_true_iff.mpr ⟨ih parts.1,by simpa [Nat.add_assoc] using parts.2⟩

theorem certified_view (views : Table View) (nodes : Table Node)
    (roots : passBlock (checkRootAt views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : (get views i) = some v) : ViewOK v := by
  apply whole_sound views nodes _ _ i v hv
  · intro j w hw
    have hj : j < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hw
    have ok := block_at _ roots (i := j) (Nat.zero_le _) (by omega)
    simpa [checkRootAt,hw] using ok
  · intro j a ha
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok

end SignedProjection.QFast
namespace SignedProjection.QFast

def rowAt (m : Array Nat) (k : Fin 64) := Fin.ofNat 64 (m[k.val]?.getD 0)
def rowWord (m : Array Nat) (w : Word) : Word :=
  (BitVec.ofBoolListLE (List.ofFn (fun k : Fin 64 => w[(rowAt m k).val]))).cast List.length_ofFn

theorem rowWord_bit (m : Array Nat) (w : Word) (j : Nat) (hj : j < 64) :
    (rowWord m w)[j] = w[(rowAt m ⟨j,hj⟩).val] := by
  rw [← BitVec.getLsbD_eq_getElem hj]
  simp only [rowWord, BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE,
    List.getD_eq_getElem?_getD, List.getElem?_ofFn, hj, dite_true, Option.getD_some]

theorem rowWord_and (m : Array Nat) (x y : Word) : rowWord m (x &&& y) = rowWord m x &&& rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_and]
theorem rowWord_or (m : Array Nat) (x y : Word) : rowWord m (x ||| y) = rowWord m x ||| rowWord m y :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_or]
theorem rowWord_not (m : Array Nat) (x : Word) : rowWord m (~~~x) = ~~~rowWord m x :=
  BitVec.eq_of_getElem_eq fun j hj => by simp only [rowWord_bit,BitVec.getElem_not]

def viewMap (m : Array Nat) (v : View) (w : Word) := signedPin (vm v) (va v) (rowWord m w)
theorem viewMap_ops (m : Array Nat) (v : View) {a b c : Word} (hc : c ∈ signedOps a b) :
    viewMap m v c ∈ signedOps (viewMap m v a) (viewMap m v b) := by
  apply signedPin_ops
  simp only [signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hc ⊢
  rcases hc with rfl|rfl|rfl|rfl
  · exact Or.inl (rowWord_and ..)
  · exact Or.inr (Or.inl (rowWord_or ..))
  · exact Or.inr (Or.inr (Or.inl (by rw [rowWord_and,rowWord_not])))
  · exact Or.inr (Or.inr (Or.inr (by rw [rowWord_and,rowWord_not])))

def viewAliasOK (m : Array Nat) (src dst : View) : Bool :=
  (vg dst != 0) && (viewMap m dst (vg src) == vg dst) && decide (vk src ≤ vk dst) &&
  (vs src).all fun w => viewMap m dst w == 0 || (vs dst).contains (viewMap m dst w)

theorem viewAlias_sound {m : Array Nat} {src dst : View} (yes : ViewOK dst)
    (valid : viewAliasOK m src dst = true) : ViewOK src := by
  simp only [viewAliasOK,Bool.and_eq_true, bne_iff_ne,beq_iff_eq,decide_eq_true_eq] at valid
  obtain ⟨⟨⟨nz,go⟩,le⟩,all⟩ := valid
  intro run
  obtain ⟨S,sub,path⟩ := CoreSigned.compress run
  have ng := fun h : viewMap m dst (vg src) = 0 => nz (go.symm.trans h)
  obtain ⟨j,hj,T,ts,tail⟩ := projected (viewMap m dst) signedOps signedOps _ ng
    (viewMap_ops m dst) zero_left zero_right equal_inputs path
  have supply : T ⊆ (vs dst).toFinset := by
    intro y hy
    obtain ⟨pn,w,hw,rfl⟩ := (avail_mem _).mp (ts hy)
    have h := List.all_eq_true.mp all w (List.mem_toFinset.mp (sub hw))
    simp only [Bool.or_eq_true,beq_iff_eq] at h
    exact List.mem_toFinset.mpr (List.contains_iff_mem.mp (h.resolve_left pn))
  rw [go] at tail
  exact yes (pad_build (by omega) (live_build tail supply))

abbrev AliasTable := Nat → Option (Nat × Array Nat)
def symCheckRoot (aliases : AliasTable) (views : Table View) (nodes : Table Node) (i : Nat) : Bool :=
  match get views i with
  | none => true
  | some v => match aliases i with
    | none => evalRoot views nodes i v
    | some (j,m) => decide (j < i) &&
      match get views j with
      | none => false
      | some w => viewAliasOK m v w

theorem symCertified (aliases : AliasTable) (views : Table View) (nodes : Table Node)
    (roots : passBlock (symCheckRoot aliases views nodes) 0 views.1 = true)
    (states : passBlock (checkNodeAt views nodes) 0 nodes.1 = true)
    {i : Nat} {v : View} (hv : get views i = some v) : ViewOK v := by
  have allNodes (j : Nat) (a : Node) (ha : get nodes j = some a) : evalNode views nodes a = true := by
    have hj : j < nodes.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at ha
    have ok := block_at _ states (i := j) (Nat.zero_le _) (by omega)
    simpa [checkNodeAt,ha] using ok
  induction i using Nat.strong_induction_on generalizing v with
  | ind i ih =>
    have hi : i < views.1 := by by_contra! lo; simp [get, Nat.not_lt_of_ge lo] at hv
    have ok := block_at _ roots (i := i) (Nat.zero_le _) (by omega)
    simp only [symCheckRoot,hv] at ok
    cases he : aliases i with
    | none =>
      exact view_from_earlier views nodes i v hv ih (by simpa only [he] using ok) allNodes
    | some x =>
      rcases x with ⟨j,m⟩
      simp only [he,Bool.and_eq_true,decide_eq_true_eq] at ok
      cases hh : get views j with
      | none => simp [hh] at ok
      | some w => exact viewAlias_sound (ih j ok.1 hh) (by simpa only [hh] using ok.2)

end SignedProjection.QFast

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def witness : Circuit :=
  ⟨[⟨.or,[1,2]⟩, ⟨.and,[4,6]⟩, ⟨.and,[1,2]⟩, ⟨.or,[5,7]⟩, ⟨.and,[6,0]⟩, ⟨.or,[3,10]⟩, ⟨.and,[11,9]⟩, ⟨.or,[8,12]⟩, ⟨.or,[7,0]⟩, ⟨.and,[12,8]⟩, ⟨.or,[14,15]⟩, ⟨.and,[16,13]⟩],17⟩

theorem size : witness.size = 12 := rfl

theorem monotone : Monotone2 witness := by
  simp [Monotone2,witness]

set_option maxRecDepth 32000 in
theorem correct : ∀ x : Fin 6 → Bool, witness.eval (List.ofFn x) =
    Nat.testBit (4276677288 * 2 ^ 32 + 4243095680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  decide +kernel

end LowerSymSix

namespace Direct64
open PEqualNP.CircuitLowerBounds SignedProjection
abbrev W := BitVec 64
abbrev basicOps (a b : W) := signedOps a b
abbrev goal : W := ~~~0xfee8eaa8fce88080
open CoreSigned (build)
def tableB (x : Fin 6 → Bool) :=
  Nat.testBit (4276677288 * 2 ^ 32 + 4243095680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 64 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 64)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,SignedProjection.signedOps] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

set_option maxRecDepth 100000 in
theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 64) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private theorem read_bit (w : List W) (i : ℕ) (k : Fin 64) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 100000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 64) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#64)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 100000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

def cols : List W := [0xaaaaaaaaaaaaaaaa, 0xcccccccccccccccc, 0xf0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00, 0xffff0000ffff0000, 0xffffffff00000000]

theorem sample64 : ∀ k : Fin 64, tableB (fun i => (cols.getD i.val 0)[k.val]) = (~~~goal)[k.val] := by
  decide +kernel

theorem zero_open (k : ℕ) {t : W} (av : Finset W) (hz : ∀ u ∈ av, u.getLsbD 0 = false)
    (h : build basicOps t k av) : t.getLsbD 0 = false := by
  induction k generalizing av with
  | zero => exact hz t h
  | succ k ih =>
    rcases h with skip | ⟨a,ha,b,hb,_,z,hop,tail⟩
    · exact ih av hz skip
    · apply ih (insert z av) _ tail
      intro u hu
      rcases Finset.mem_insert.mp hu with rfl|hu
      · simp only [basicOps,signedOps,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hop
        rcases hop with rfl|rfl|rfl|rfl <;> simp only [BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,hz a ha,hz b hb,Bool.false_and,Bool.or_self]
      · exact hz u hu

theorem low (reject : ¬ build basicOps (0xfee8eaa8fce88080 : W) 10 cols.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = tableB x) : 10 < binaryCost gs := by
  by_contra! low
  have width : cols.length = 6 := rfl
  have init : ∀ u ∈ cols, holds cols.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 64) :
      (gs.foldl step (cols.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (cols.getD i.val 0)
    have same : List.ofFn x = cols.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < cols.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (cols.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample64 k
  obtain ⟨t, ht, run⟩ := compile gs o hg cols cols.toFinset init evaluate

  have h0 : ∀ u ∈ cols.toFinset, u.getLsbD 0 = false := by
    intro u hu
    simp only [cols,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at hu
    rcases hu with rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel
  rcases ht with rfl|rfl
  · have odd : goal.getLsbD 0 ≠ false := by decide +kernel
    exact odd (zero_open _ _ h0 run)
  · apply reject
    apply pad_build low
    exact run
end Direct64

namespace LowerSymSix
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
theorem finish
    (reject : ¬ CoreSigned.build SignedProjection.signedOps (0xfee8eaa8fce88080 : BitVec 64) 10 Direct64.cols.toFinset) :
∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 4243095680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4243095680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨C, hg, hs, he⟩
  by_cases neg : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, hm, op⟩ := neg
    have lo := Direct64.low reject C.gates C.output hg he
    have proper : Direct64.binaryCost C.gates < C.gates.length := by
      apply List.length_filter_lt_length_iff_exists.mpr
      exact ⟨g, hm, by simp [Direct64.isBinary, op]⟩
    have cap : C.gates.length ≤ s := hs
    exact ⟨witness, monotone, by rw [size]; omega, correct⟩
  · refine ⟨C, ?_, hs, he⟩
    intro g hm
    obtain ⟨hop, hin⟩ := hg g hm
    refine ⟨?_, hin⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (neg ⟨g, hm, h⟩).elim

end LowerSymSix

namespace SignedProjection

def ew0 : Word := 0x4040404000000000
def ew1 : Word := 0x4400440000000000
def ew2 : Word := 0x4444000000000000
def ew3 : Word := 0x5000500000000000
def ew4 : Word := 0x5050000000000000
def ew5 : Word := 0x5500000000000000
def ew6 : Word := 0x4444444400000000
def ew7 : Word := 0x5050505000000000
def ew8 : Word := 0x5500550000000000
def ew9 : Word := 0x5555000000000000
def ew10 : Word := 0x4444444444444444
def ew11 : Word := 0x5050505050505050
def ew12 : Word := 0x5500550055005500
def ew13 : Word := 0x5555000055550000
def ew14 : Word := 0x5555555500000000
def ew15 : Word := 0x444400000000
def ew16 : Word := 0x404040400000000
def ew17 : Word := 0x444400004444
def ew18 : Word := 0x404040404040404
def ew19 : Word := 0x4400440044004400
def ew20 : Word := 0xc000000000c
def ew21 : Word := 0x400040000040004
def ew22 : Word := 0xc000c0000000000
def ew23 : Word := 0xc0c00000c0c
def ew24 : Word := 0xc000c000c000c00
def ew25 : Word := 0xc0c0c0c00000000
def ew26 : Word := 0xc000c
def ew27 : Word := 0x440044
def ew28 : Word := 0xcc0000
def ew29 : Word := 0xc0000000c00
def ew30 : Word := 0x440000004400
def ew31 : Word := 0xcc0000000000
def ew32 : Word := 0xcc000000cc00
def ew33 : Word := 0xcccc00000000
def ew34 : Word := 0x44004400000000
def ew35 : Word := 0xc0c0c0c0c0c0c0c
def ew36 : Word := 0xcc00cc00cc00cc00
def ew37 : Word := 0xcccc0000cccc0000
def ew38 : Word := 0xcccccccc00000000
def ew39 : Word := 0xa0000000a
def ew40 : Word := 0x200000202000002
def ew41 : Word := 0xa00000a00000000
def ew42 : Word := 0x2200000022
def ew43 : Word := 0x2200002200000000
def ew44 : Word := 0xaa00000000
def ew45 : Word := 0xa00000a
def ew46 : Word := 0x22000022
def ew47 : Word := 0xaa000000
def ew48 : Word := 0xa00000a0a00000a
def ew49 : Word := 0x2200002222000022
def ew50 : Word := 0xaa000000aa000000
def ew51 : Word := 0xaa0000aa00000000
def ew52 : Word := 0xa0a0a0a0a0a0a0a
def ew53 : Word := 0x2222222222222222
def ew54 : Word := 0xaa00aa00aa00aa00
def ew55 : Word := 0xaaaa0000aaaa0000
def ew56 : Word := 0xaaaaaaaa00000000
def ew57 : Word := 0x3030303030303030
def ew58 : Word := 0xf000f000f000f000
def ew59 : Word := 0xf0f00000f0f00000
def ew60 : Word := 0xf0f0f0f000000000
def ew61 : Word := 0x550000005500
def ew62 : Word := 0x1100110011001100
def ew63 : Word := 0x5000500050005000
def ew64 : Word := 0x33003300000000
def ew65 : Word := 0x55005500000000
def ew66 : Word := 0xf000f000000000
def ew67 : Word := 0xff000000000000
def ew68 : Word := 0x303000003030000
def ew69 : Word := 0x1111000011110000
def ew70 : Word := 0x3300000033000000
def ew71 : Word := 0x3333000000000000
def ew72 : Word := 0x505000005050000
def ew73 : Word := 0xf0000000f000000
def ew74 : Word := 0xf0f000000000000
def ew75 : Word := 0x880000008800
def ew76 : Word := 0xc0000000c000
def ew77 : Word := 0x88008800
def ew78 : Word := 0xa000a000
def ew79 : Word := 0xff000000ff000000
def ew80 : Word := 0xff00ff0000000000
def ew81 : Word := 0xaa00aa
def ew82 : Word := 0xcc00cc
def ew83 : Word := 0xf000f0
def ew84 : Word := 0xff0000
def ew85 : Word := 0xf0f0000000000000
def ew86 : Word := 0xff00000000000000
def ew87 : Word := 0x882200008822
def ew88 : Word := 0xc0300000c030
def ew89 : Word := 0xcc3300000000
def ew90 : Word := 0xaaaa0000aaaa
def ew91 : Word := 0xcccc0000cccc
def ew92 : Word := 0xf0f00000f0f0
def ew93 : Word := 0xff000000ff00
def ew94 : Word := 0xffff00000000
def ew95 : Word := 0x8800880088008800
def ew96 : Word := 0xa000a000a000a000
def ew97 : Word := 0xaa00aa0000000000
def ew98 : Word := 0x8800000088
def ew99 : Word := 0xa0000000a0
def ew100 : Word := 0x888800008888
def ew101 : Word := 0xa0a00000a0a0
def ew102 : Word := 0xaa000000aa00
def ew103 : Word := 0xaaaa00000000
def ew104 : Word := 0x505000005050
def ew105 : Word := 0x1010101010101010
def ew106 : Word := 0x88008800880088
def ew107 : Word := 0xc000c000c000c0
def ew108 : Word := 0xcc000000cc0000
def ew109 : Word := 0xcc00cc00000000
def ew110 : Word := 0x303000003030
def ew111 : Word := 0x3000300030003000
def ew112 : Word := 0x3030303000000000
def ew113 : Word := 0xc000c000c000c000
def ew114 : Word := 0xf0000000f0000000
def ew115 : Word := 0xf000f00000000000
def ew116 : Word := 0xcc000000cc000000
def ew117 : Word := 0xcc00cc0000000000
def ew118 : Word := 0x2200880022008800
def ew119 : Word := 0x3000c0003000c000
def ew120 : Word := 0x3300cc0000000000
def ew121 : Word := 0xa0000000a000
def ew122 : Word := 0xf00000000000
def ew123 : Word := 0xf0000000f000
def ew124 : Word := 0xf0f000000000
def ew125 : Word := 0x300300003003
def ew126 : Word := 0x500500005005
def ew127 : Word := 0xf00f00000000
def ew128 : Word := 0x30300000000
def ew129 : Word := 0x414100000000
def ew130 : Word := 0xc30000000000
def ew131 : Word := 0x121200000000
def ew132 : Word := 0x505000000000
def ew133 : Word := 0x5a0000000000
def ew134 : Word := 0x300300000000
def ew135 : Word := 0x500500000000
def ew136 : Word := 0x60600000000
def ew137 : Word := 0x660000000000
def ew138 : Word := 0xc0300000000
def ew139 : Word := 0x441100000000
def ew140 : Word := 0x50a00000000
def ew141 : Word := 0x112200000000
def ew142 : Word := 0x550000000000
def ew143 : Word := 0xf0f00000000
def ew144 : Word := 0x333300000000
def ew145 : Word := 0x555500000000
def ew146 : Word := 0xff0000000000
def ew147 : Word := 0xc0300000c03
def ew148 : Word := 0x441100004411
def ew149 : Word := 0x5a5a
def ew150 : Word := 0x121200001212
def ew151 : Word := 0x5a0000005a00
def ew152 : Word := 0xf0000000f
def ew153 : Word := 0x3300000033
def ew154 : Word := 0x5500000055
def ew155 : Word := 0xff00000000
def ew156 : Word := 0x6666
def ew157 : Word := 0x60600000606
def ew158 : Word := 0x660000006600
def ew159 : Word := 0x112200001122
def ew160 : Word := 0x50a0000050a0
def ew161 : Word := 0x55aa00000000
def ew162 : Word := 0xf0f00000f0f
def ew163 : Word := 0x333300003333
def ew164 : Word := 0x555500005555
def ew165 : Word := 0x88888888
def ew166 : Word := 0xc0c0c0c0
def ew167 : Word := 0xcc00cc00
def ew168 : Word := 0xcccc0000
def ew169 : Word := 0x2000002020000020
def ew170 : Word := 0x2200000022000000
def ew171 : Word := 0x2020202020202020
def ew172 : Word := 0x2200220022002200
def ew173 : Word := 0x2222000022220000
def ew174 : Word := 0x2222222200000000
def ew175 : Word := 0x303030300000000
def ew176 : Word := 0x1111111100000000
def ew177 : Word := 0x3300330000000000
def ew178 : Word := 0xaaaaaaaaaaaaaaaa
def ew179 : Word := 0xcccccccccccccccc
def ew180 : Word := 0xf0f0f0f0f0f0f0f0
def ew181 : Word := 0xff00ff00ff00ff00
def ew182 : Word := 0xffff0000ffff0000
def ew183 : Word := 0xffffffff00000000
def ew184 : Word := 0x4000400000000000
def ew185 : Word := 0x1555000000000000
def ew186 : Word := 0x1500150000000000
def ew187 : Word := 0x4040000000000000
def ew188 : Word := 0x1500550000000000
def ew189 : Word := 0x1515000000000000
def ew190 : Word := 0x1050105000000000
def ew191 : Word := 0x4400000000000000
def ew192 : Word := 0x1050505000000000
def ew193 : Word := 0x1155000000000000
def ew194 : Word := 0x1010505000000000
def ew195 : Word := 0x1100550000000000
def ew196 : Word := 0x444044400000000
def ew197 : Word := 0x5000000000000000
def ew198 : Word := 0x444444400000000
def ew199 : Word := 0x555000000000000
def ew200 : Word := 0x404444400000000
def ew201 : Word := 0x500550000000000
def ew202 : Word := 0x44444400000000
def ew203 : Word := 0x50505000000000
def ew204 : Word := 0xcccc0404cccc0404
def ew205 : Word := 0x40400000404
def ew206 : Word := 0xc8c8c8c800000000
def ew207 : Word := 0xcccc0c0ccccc0c0c
def ew208 : Word := 0x404cccc04040404
def ew209 : Word := 0x4040404040404040
def ew210 : Word := 0xcccc4040cccc4040
def ew211 : Word := 0x4444040444440404
def ew212 : Word := 0x4444404044444040
def ew213 : Word := 0xcc00c000cc00c000
def ew214 : Word := 0x44004c0c44004c0c
def ew215 : Word := 0x44004400440044
def ew216 : Word := 0xc0c08080c0c0808
def ew217 : Word := 0xcccccccccccc0000
def ew218 : Word := 0xaa000002aa000002
def ew219 : Word := 0x200000002
def ew220 : Word := 0xaa0000aa00000002
def ew221 : Word := 0xaa0000aa02000002
def ew222 : Word := 0x2000002
def ew223 : Word := 0xaa000000aa000002
def ew224 : Word := 0x2200002022000020
def ew225 : Word := 0xaa0000aa0000000a
def ew226 : Word := 0xa
def ew227 : Word := 0x2200002222000020
def ew228 : Word := 0xaa0000aaaa000000
def ew229 : Word := 0x2200002220000020
def ew230 : Word := 0xaa000000aa00000a
def ew231 : Word := 0xa0000080a000008
def ew232 : Word := 0xaa0000aa00000022
def ew233 : Word := 0x22
def ew234 : Word := 0xa00000a0a000008
def ew235 : Word := 0xa00000a08000008
def ew236 : Word := 0xaa000000aa000022
def ew237 : Word := 0xa00000a0a000000
def ew238 : Word := 0x2200002222000000
def ew239 : Word := 0xb0b0b0b0b0b0b0b0
def ew240 : Word := 0x8c8c8c8c8c8c8c8c
def ew241 : Word := 0x3f3f00003f3f
def ew242 : Word := 0x5f5f00005f5f
def ew243 : Word := 0x3f3f00000000
def ew244 : Word := 0xa0a00000000
def ew245 : Word := 0xf00000000
def ew246 : Word := 0x222200000000
def ew247 : Word := 0x3300000000
def ew248 : Word := 0xff5500000000
def ew249 : Word := 0x777700007777
def ew250 : Word := 0x2a2a00002a2a
def ew251 : Word := 0x4c4c00004c4c
def ew252 : Word := 0x707000007070
def ew253 : Word := 0xc0c0c0c0c0c0c0c0
def ew254 : Word := 0xeaeaeaeaeaeaeaea
def ew255 : Word := 0xfcfcfcfcfcfcfcfc

def labelsBlock0 : Array Nat := #[3, 8888, 9912, 10936, 9944, 13, 8376, 9400, 10424, 11448, 5, 88, 600, 1112, 1624, 4184]
def labelsBlock1 : Array Nat := #[4696, 5208, 4712, 3768, 4126, 13976, 11928, 14024, 189, 5656, 11800, 5704, 11832, 6728, 4134, 4876]
def labelsBlock2 : Array Nat := #[8972, 4936, 4142, 1804, 1816, 181, 6924, 1812, 309, 10628, 4218, 2108, 2364, 2620, 2876, 3132]
def labelsBlock3 : Array Nat := #[3388, 3644, 2664, 2468, 485, 28, 284, 540, 796, 1052, 1308, 1564, 908, 8612, 4270, 2924]
def labelsBlock4 : Array Nat := #[4254, 4290, 497, 10116, 9092, 9604, 10136, 517, 9112, 4362, 505, 340, 1364, 4436, 1428, 4418]
def labelsBlock5 : Array Nat := #[844, 1, 5204, 4130, 4182, 305, 4684, 4282, 489, 3612, 4342, 1596, 4278, 4346, 588, 4410]
def labelsBlock6 : Array Nat := #[9756, 8844, 652, 4428, 593, 5232, 3356, 1340, 332, 12620, 8588, 396, 2844, 828, 12628, 8596]
def labelsBlock7 : Array Nat := #[2892, 616, 12904, 9816, 6628, 14568, 14576, 9, 4098, 4114, 13528, 13552, 65, 4118, 11504, 101]
def labelsBlock8 : Array Nat := #[9432, 4122, 13016, 13032, 121, 10984, 153, 8920, 169, 4102, 17, 4110, 25, 29, 4106, 37]
def labelsBlock9 : Array Nat := #[41, 12520, 49, 10472, 57, 61, 21, 12504, 8936, 33, 45, 12528, 8408, 8424, 8432, 53]
def labelsBlock10 : Array Nat := #[10480, 69, 73, 81, 85, 93, 97, 77, 89, 9456, 105, 109, 113, 117, 125, 129]
def labelsBlock11 : Array Nat := #[137, 141, 149, 133, 145, 157, 161, 165, 173, 177, 185, 4138, 229, 4170, 3852, 3884]
def labelsBlock12 : Array Nat := #[4174, 1836, 4178, 5900, 245, 257, 9996, 11944, 4166, 281, 3864, 3896, 1848, 285, 5912, 289]
def labelsBlock13 : Array Nat := #[10008, 4908, 6956, 9004, 11052, 11020, 5784, 297, 301, 4146, 4150, 4154, 4158, 6696, 193, 197]
def labelsBlock14 : Array Nat := #[4162, 201, 205, 209, 217, 221, 15016, 15048, 16024, 16072, 5640, 4872, 6664, 6824, 9096, 5443626]
def labelsBlock15 : Array Nat := #[5960, 7752, 13896, 5644, 5932, 7948, 6712, 213, 5688, 7704, 6700, 1864, 3912, 10056, 6984, 13128]
def labelsBlock16 : Array Nat := #[225, 8968, 1800, 233, 237, 11176, 9128, 241, 8008, 249, 253, 261, 265, 269, 277, 7736]
def labelsBlock17 : Array Nat := #[5374034, 273, 7688, 11784, 6668, 13848, 4329554, 6426706, 10040, 293, 13256, 6488106, 7832, 4390954, 4222, 4226]
def labelsBlock18 : Array Nat := #[481, 4258, 4262, 4266, 4274, 10404, 4180, 11412, 9364, 1108, 13396, 1172, 7405750, 7405754, 4286, 4294]
def labelsBlock19 : Array Nat := #[4238, 313, 7012, 7524, 4194, 4206, 7444, 4210, 365, 9492, 4214, 401, 7956, 421, 10004, 453]
def labelsBlock20 : Array Nat := #[14692, 14724, 469, 4186, 4190, 4198, 317, 321, 4202, 329, 333, 341, 349, 357, 361, 7428]
def labelsBlock21 : Array Nat := #[6916, 14596, 325, 8964, 9476, 337, 8036, 15716, 345, 1892, 10084, 15748, 353, 8068, 1924, 15204]
def labelsBlock22 : Array Nat := #[15236, 369, 373, 377, 385, 393, 397, 1796, 15116, 381, 389, 7556, 9572, 405, 409, 413]
def labelsBlock23 : Array Nat := #[417, 425, 429, 433, 441, 449, 437, 445, 7044, 9060, 457, 461, 465, 473, 477, 6248]
def labelsBlock24 : Array Nat := #[10892, 12876, 7405602, 5308502, 4230, 4234, 7405598, 7405698, 12888, 4242, 6256, 2920, 14564, 2212, 4246, 3184]
def labelsBlock25 : Array Nat := #[2152, 4250, 14440, 2988, 3688, 14448, 3508, 10856, 493, 4172, 7405654, 7471286, 6357026, 5308546, 4298, 4302]
def labelsBlock26 : Array Nat := #[4306, 6357022, 4310, 13400, 501, 4318, 4330, 4334, 4338, 6508, 6252, 6516, 6260, 4314, 4322, 3704]
def labelsBlock27 : Array Nat := #[4326, 2160, 4350, 509, 577, 4354, 4398, 4382, 9624, 9616, 11952, 585, 3860, 3892, 4386, 1844]
def labelsBlock28 : Array Nat := #[4406, 513, 11652, 7471362, 5308702, 569, 11140, 7471394, 4390, 573, 4394, 10664, 521, 525, 4358, 529]
def labelsBlock29 : Array Nat := #[533, 4366, 537, 541, 4370, 545, 549, 4374, 553, 557, 561, 12184, 565, 4378, 10656, 10120]
def labelsBlock30 : Array Nat := #[10128, 11920, 11696, 11144, 11912, 11664, 12200, 9608, 9488, 1808, 5374254, 5374238, 581, 589, 4402, 5378350]
def labelsBlock31 : Array Nat := #[5378334, 4259874, 597, 4329718, 4329654, 5308730, 4259870, 4426, 6476, 4200, 6484, 5308542, 9884, 1692, 4259970, 6357118]
def labelsBlock32 : Array Nat := #[4259926, 7405694, 5637279926, 601, 4329634, 4329650, 9868, 5435883550, 4414, 4422]

def labelsGet (i : Nat) : Nat :=
  if i < 256 then
    if i < 128 then
      if i < 64 then
        if i < 32 then
          if i < 16 then
            labelsBlock0.getD (i-0) 3
          else
            labelsBlock1.getD (i-16) 3
        else
          if i < 48 then
            labelsBlock2.getD (i-32) 3
          else
            labelsBlock3.getD (i-48) 3
      else
        if i < 96 then
          if i < 80 then
            labelsBlock4.getD (i-64) 3
          else
            labelsBlock5.getD (i-80) 3
        else
          if i < 112 then
            labelsBlock6.getD (i-96) 3
          else
            labelsBlock7.getD (i-112) 3
    else
      if i < 192 then
        if i < 160 then
          if i < 144 then
            labelsBlock8.getD (i-128) 3
          else
            labelsBlock9.getD (i-144) 3
        else
          if i < 176 then
            labelsBlock10.getD (i-160) 3
          else
            labelsBlock11.getD (i-176) 3
      else
        if i < 224 then
          if i < 208 then
            labelsBlock12.getD (i-192) 3
          else
            labelsBlock13.getD (i-208) 3
        else
          if i < 240 then
            labelsBlock14.getD (i-224) 3
          else
            labelsBlock15.getD (i-240) 3
  else
    if i < 384 then
      if i < 320 then
        if i < 288 then
          if i < 272 then
            labelsBlock16.getD (i-256) 3
          else
            labelsBlock17.getD (i-272) 3
        else
          if i < 304 then
            labelsBlock18.getD (i-288) 3
          else
            labelsBlock19.getD (i-304) 3
      else
        if i < 352 then
          if i < 336 then
            labelsBlock20.getD (i-320) 3
          else
            labelsBlock21.getD (i-336) 3
        else
          if i < 368 then
            labelsBlock22.getD (i-352) 3
          else
            labelsBlock23.getD (i-368) 3
    else
      if i < 448 then
        if i < 416 then
          if i < 400 then
            labelsBlock24.getD (i-384) 3
          else
            labelsBlock25.getD (i-400) 3
        else
          if i < 432 then
            labelsBlock26.getD (i-416) 3
          else
            labelsBlock27.getD (i-432) 3
      else
        if i < 480 then
          if i < 464 then
            labelsBlock28.getD (i-448) 3
          else
            labelsBlock29.getD (i-464) 3
        else
          if i < 496 then
            labelsBlock30.getD (i-480) 3
          else
            if i < 512 then
              labelsBlock31.getD (i-496) 3
            else
              labelsBlock32.getD (i-512) 3

def decodeHints (enc i : Nat) := labelsGet ((enc >>> (i * 10)) % 1024)

def localHints (stride dict enc i : Nat) : Nat :=
  let q := (enc >>> (stride*i)) % (2^stride)
  labelsGet ((dict >>> (10*q)) % 1024)

def viewsBlock0 : Array View := #[
  ⟨0x4444444400000000,⟨34,by decide⟩,0x4440400000000000,[ew0,ew1,ew2],3,localHints 3 0x50100300801 0x888688⟩,
  ⟨0x5050505000000000,⟨36,by decide⟩,0x5040400000000000,[ew0,ew3,ew4],2,(fun _ => 3)⟩,
  ⟨0x5555000000000000,⟨48,by decide⟩,0x5440000000000000,[ew2,ew4,ew5],2,(fun _ => 3)⟩,
  ⟨0x5500550000000000,⟨40,by decide⟩,0x5400400000000000,[ew1,ew3,ew5],2,(fun _ => 3)⟩,
  ⟨0x5050505000000000,⟨36,by decide⟩,0x5040400000000000,[ew0,ew3,ew4],3,(fun _ => 3)⟩,
  ⟨0x5500550000000000,⟨40,by decide⟩,0x5400400000000000,[ew1,ew3,ew5],3,(fun _ => 3)⟩,
  ⟨0x5555000000000000,⟨48,by decide⟩,0x5440000000000000,[ew2,ew4,ew5],3,(fun _ => 3)⟩,
  ⟨0x5555555500000000,⟨32,by decide⟩,0x5440400000000000,[ew6,ew7,ew8,ew9],6,localHints 4 0xa0100900c080080700406 0x8654321076543210⟩,
  ⟨0x5555555555555555,⟨0,by decide⟩,0x5440400054400000,[ew10,ew11,ew12,ew13,ew14],7,localHints 4 0x5013048110400f0380d0300b 0x96547654321032108654765432103210⟩,
  ⟨0x4444444400000000,⟨54,by decide⟩,0x4044400000000,[ew15,ew16,ew1],3,localHints 2 0x601705815 0xc844⟩,
  ⟨0x4444444444444444,⟨22,by decide⟩,0x4044400044444,[ew17,ew18,ew19,ew6],4,localHints 3 0x781d0701b06819 0xa10810610208⟩,
  ⟨0xc000c00000c000c,⟨19,by decide⟩,0x4000004000c,[ew20,ew21,ew22],3,(fun _ => 3)⟩,
  ⟨0xc0c0c0c0c0c0c0c,⟨19,by decide⟩,0x4040400040c0c,[ew23,ew18,ew24,ew25],3,localHints 3 0x22074210801f 0x810610208208⟩,
  ⟨0xcc00cc,⟨7,by decide⟩,0x4004c,[ew26,ew27,ew28],2,(fun _ => 3)⟩,
  ⟨0xcc000000cc00,⟨15,by decide⟩,0x40000004c00,[ew29,ew30,ew31],2,(fun _ => 3)⟩,
  ⟨0xcccc0000cccc,⟨7,by decide⟩,0x44400004c4c,[ew23,ew17,ew32,ew33],3,(fun _ => 3)⟩
]

def viewsBlock1 : Array View := #[
  ⟨0x4444444400000000,⟨46,by decide⟩,0x4044400000000,[ew34,ew16,ew2],2,(fun _ => 3)⟩,
  ⟨0x4444444400000000,⟨46,by decide⟩,0x4044400000000,[ew34,ew16,ew2],3,(fun _ => 3)⟩,
  ⟨0xcc00cc,⟨7,by decide⟩,0x4004c,[ew26,ew27,ew28],3,(fun _ => 3)⟩,
  ⟨0xcc000000cc00,⟨15,by decide⟩,0x40000004c00,[ew29,ew30,ew31],3,(fun _ => 3)⟩,
  ⟨0xcccc0000cccc,⟨7,by decide⟩,0x44400004c4c,[ew23,ew17,ew32,ew33],4,(fun _ => 3)⟩,
  ⟨0xcccccccccccccccc,⟨7,by decide⟩,0x4044400044c4c,[ew35,ew10,ew36,ew37,ew38],7,localHints 3 0x941d0902007c23 0xa18818208208410410208208⟩,
  ⟨0xa00000a0a00000a,⟨27,by decide⟩,0x20200000a,[ew39,ew40,ew41],2,(fun _ => 3)⟩,
  ⟨0x2200002222000022,⟨29,by decide⟩,0x202000022,[ew42,ew40,ew43],2,(fun _ => 3)⟩,
  ⟨0xa00000a0a00000a,⟨27,by decide⟩,0x20200000a,[ew39,ew40,ew41],3,(fun _ => 3)⟩,
  ⟨0xaa000000aa,⟨7,by decide⟩,0x20000002a,[ew39,ew42,ew44],2,(fun _ => 3)⟩,
  ⟨0xaa0000aa,⟨7,by decide⟩,0x200002a,[ew45,ew46,ew47],2,(fun _ => 3)⟩,
  ⟨0x2200002222000022,⟨29,by decide⟩,0x202000022,[ew42,ew40,ew43],3,(fun _ => 3)⟩,
  ⟨0xaa000000aa,⟨7,by decide⟩,0x20000002a,[ew39,ew42,ew44],3,(fun _ => 3)⟩,
  ⟨0xaa0000aa,⟨7,by decide⟩,0x200002a,[ew45,ew46,ew47],3,(fun _ => 3)⟩,
  ⟨0xaa0000aaaa0000aa,⟨7,by decide⟩,0x20200002a,[ew48,ew49,ew50,ew51],6,localHints 3 0x2809c2009823 0x818208410208⟩,
  ⟨0xaaaaaaaaaaaaaaaa,⟨7,by decide⟩,0x2000202022a2a,[ew52,ew53,ew54,ew55,ew56],6,localHints 3 0xa82909c2007c23 0xa18818208208410410208208⟩
]

def viewsBlock2 : Array View := #[
  ⟨0xf0f0f0f0f0f0f0f0,⟨7,by decide⟩,0x10105000107070,[ew57,ew11,ew58,ew59,ew60],6,(fun _ => 3)⟩,
  ⟨0x5500550055005500,⟨26,by decide⟩,0x100150001005500,[ew61,ew62,ew63,ew8],4,(fun _ => 3)⟩,
  ⟨0xff00ff00000000,⟨35,by decide⟩,0x17005700000000,[ew64,ew65,ew66,ew67],4,(fun _ => 3)⟩,
  ⟨0x3333000033330000,⟨21,by decide⟩,0x113000003130000,[ew68,ew69,ew70,ew71],4,(fun _ => 3)⟩,
  ⟨0xf0f00000f0f0000,⟨19,by decide⟩,0x107000003070000,[ew68,ew72,ew73,ew74],4,(fun _ => 3)⟩,
  ⟨0xcc000000cc00,⟨10,by decide⟩,0xc80000008000,[ew75,ew76,ew31],3,(fun _ => 3)⟩,
  ⟨0xaa00aa00,⟨9,by decide⟩,0xa8008000,[ew77,ew78,ew47],2,(fun _ => 3)⟩,
  ⟨0xaa00aa00,⟨9,by decide⟩,0xa8008000,[ew77,ew78,ew47],3,(fun _ => 3)⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00ea00fc008000,[ew54,ew36,ew58,ew79,ew80],6,localHints 4 0xd0330c8310c02f0b82d0b02b 0x96543210765432108654321076543210⟩,
  ⟨0xff00ff,⟨0,by decide⟩,0xe80080,[ew81,ew82,ew83,ew84],5,(fun _ => 3)⟩,
  ⟨0xffff000000000000,⟨51,by decide⟩,0x117000000000000,[ew71,ew9,ew85,ew86],5,(fun _ => 3)⟩,
  ⟨0xcc330000cc33,⟨0,by decide⟩,0xc82000008000,[ew87,ew88,ew32,ew89],6,(fun _ => 3)⟩,
  ⟨0xffff0000ffff,⟨0,by decide⟩,0xeaa800008080,[ew90,ew91,ew92,ew93,ew94],6,localHints 4 0xf83d0f03b0e8390e0370d835 0x96543210865432107654321076543210⟩,
  ⟨0xff00ff,⟨0,by decide⟩,0xe80080,[ew81,ew82,ew83,ew84],6,(fun _ => 3)⟩,
  ⟨0xf0f0f0f0f0f0f0f0,⟨7,by decide⟩,0x10105000107070,[ew57,ew11,ew58,ew59,ew60],7,(fun _ => 3)⟩,
  ⟨0xaa00aa00aa00aa00,⟨9,by decide⟩,0xaa00aa00a8008000,[ew95,ew96,ew50,ew97],4,localHints 3 0x100330fc300b82c 0xa88688888688⟩
]

def viewsBlock3 : Array View := #[
  ⟨0xaa000000aa,⟨1,by decide⟩,0xa800000080,[ew98,ew99,ew44],3,(fun _ => 3)⟩,
  ⟨0xaaaa0000aaaa,⟨1,by decide⟩,0xaaa800008080,[ew100,ew101,ew102,ew103],4,localHints 3 0x1043d0f03a0e036 0xa88888688688⟩,
  ⟨0x5050505050505050,⟨22,by decide⟩,0x10105000105050,[ew104,ew105,ew63,ew7],3,(fun _ => 3)⟩,
  ⟨0x5050505050505050,⟨22,by decide⟩,0x10105000105050,[ew104,ew105,ew63,ew7],4,(fun _ => 3)⟩,
  ⟨0xcc00cc00cc00cc,⟨2,by decide⟩,0xc8008800c80080,[ew106,ew107,ew108,ew109],4,(fun _ => 3)⟩,
  ⟨0x3030303030303030,⟨21,by decide⟩,0x10101000103030,[ew110,ew105,ew111,ew112],3,(fun _ => 3)⟩,
  ⟨0xf000f000f000f000,⟨12,by decide⟩,0xf000e000f0008000,[ew96,ew113,ew114,ew115],3,(fun _ => 3)⟩,
  ⟨0xcc00cc00cc00cc00,⟨10,by decide⟩,0xcc00c800cc008000,[ew95,ew113,ew116,ew117],4,(fun _ => 3)⟩,
  ⟨0x3300cc003300cc00,⟨10,by decide⟩,0x3200c80030008000,[ew118,ew119,ew70,ew120],4,(fun _ => 3)⟩,
  ⟨0xff00ff0000000000,⟨40,by decide⟩,0xfe00ea0000000000,[ew97,ew117,ew115,ew86],3,(fun _ => 3)⟩,
  ⟨0xf000f000f000f000,⟨12,by decide⟩,0xf000e000f0008000,[ew96,ew113,ew114,ew115],4,(fun _ => 3)⟩,
  ⟨0xff00ff0000000000,⟨40,by decide⟩,0xfe00ea0000000000,[ew97,ew117,ew115,ew86],4,(fun _ => 3)⟩,
  ⟨0xf0000000f000,⟨12,by decide⟩,0xe00000008000,[ew121,ew76,ew122],3,(fun _ => 3)⟩,
  ⟨0xff00ff00ff00ff00,⟨8,by decide⟩,0xfe00ea00fc008000,[ew54,ew36,ew58,ew79,ew80],7,localHints 4 0x108330c8310c02f0b82d0b02b 0x96543210765432108654321076543210⟩,
  ⟨0xffff000000000000,⟨51,by decide⟩,0x117000000000000,[ew71,ew9,ew85,ew86],6,(fun _ => 3)⟩,
  ⟨0xf0f00000f0f0,⟨7,by decide⟩,0x105000007070,[ew110,ew104,ew123,ew124],4,(fun _ => 3)⟩
]

def viewsBlock4 : Array View := #[
  ⟨0xf00f0000f00f,⟨3,by decide⟩,0xe00800008000,[ew125,ew126,ew123,ew127],5,(fun _ => 3)⟩,
  ⟨0xc3c300000000,⟨39,by decide⟩,0x14300000000,[ew128,ew129,ew130],3,(fun _ => 3)⟩,
  ⟨0x5a5a00000000,⟨35,by decide⟩,0x105200000000,[ew131,ew132,ew133],3,(fun _ => 3)⟩,
  ⟨0xf00f00000000,⟨35,by decide⟩,0x100700000000,[ew134,ew135,ew122],3,(fun _ => 3)⟩,
  ⟨0x666600000000,⟨37,by decide⟩,0x44600000000,[ew136,ew15,ew137],3,(fun _ => 3)⟩,
  ⟨0xcc3300000000,⟨37,by decide⟩,0x41300000000,[ew138,ew139,ew31],3,(fun _ => 3)⟩,
  ⟨0x55aa00000000,⟨39,by decide⟩,0x150200000000,[ew140,ew141,ew142],3,(fun _ => 3)⟩,
  ⟨0xffff00000000,⟨39,by decide⟩,0x155700000000,[ew143,ew144,ew145,ew146],5,localHints 3 0x11c460a44511043 0xa88888688688⟩,
  ⟨0xcc330000cc33,⟨5,by decide⟩,0xc82000008000,[ew147,ew148,ew32,ew89],5,(fun _ => 3)⟩,
  ⟨0x5a5a00005a5a,⟨35,by decide⟩,0x105200005a5a,[ew149,ew150,ew104,ew151],4,localHints 3 0x491202911020 0x808608408408⟩,
  ⟨0xff000000ff,⟨7,by decide⟩,0x570000007f,[ew152,ew153,ew154,ew155],3,(fun _ => 3)⟩,
  ⟨0xff000000ff,⟨7,by decide⟩,0x570000007f,[ew152,ew153,ew154,ew155],4,(fun _ => 3)⟩,
  ⟨0x666600006666,⟨37,by decide⟩,0x44600006666,[ew156,ew157,ew17,ew158],4,(fun _ => 3)⟩,
  ⟨0x55aa000055aa,⟨3,by decide⟩,0x40a800000080,[ew159,ew160,ew61,ew161],6,(fun _ => 3)⟩,
  ⟨0xffff0000ffff,⟨7,by decide⟩,0x155700007f7f,[ew162,ew163,ew164,ew93,ew94],7,localHints 3 0x128290902708023 0xa10610810610208208208208⟩,
  ⟨0xcccccccc,⟨2,by decide⟩,0xccc88080,[ew165,ew166,ew167,ew168],4,(fun _ => 3)⟩
]

def viewsBlock5 : Array View := #[
  ⟨0x2200002222000022,⟨1,by decide⟩,0x2200002020000000,[ew169,ew170,ew43],3,(fun _ => 3)⟩,
  ⟨0x2222222222222222,⟨1,by decide⟩,0x2220222020200000,[ew171,ew172,ew173,ew174],3,localHints 3 0x13c3d1384d1304b 0xaa220869a208⟩,
  ⟨0x3333333300000000,⟨37,by decide⟩,0x113111300000000,[ew175,ew176,ew177,ew71],4,(fun _ => 3)⟩,
  ⟨0xffffffffffffffff,⟨0,by decide⟩,0xfee8eaa8fce88080,[ew178,ew179,ew180,ew181,ew182,ew183],10,localHints 4 0x510f0121403b0e8390e0370d835 0xa654321086543210765432107654321096543210865432107654321076543210⟩
]

def viewsGet (i : Nat) : Option View :=
  if i < 48 then
    if i < 16 then
      viewsBlock0[(i-0)]?
    else
      if i < 32 then
        viewsBlock1[(i-16)]?
      else
        viewsBlock2[(i-32)]?
  else
    if i < 64 then
      viewsBlock3[(i-48)]?
    else
      if i < 80 then
        viewsBlock4[(i-64)]?
      else
        viewsBlock5[(i-80)]?

def nodesBlock0 : Array Node := #[
  ⟨83,10,[ew178,ew179,ew180,ew181,ew182,ew183],localHints 6 0x41d0730cc721c4321c06f1b86d0b86c1ac6a1a44e1a04c19c30198650d86413463188141843c1801317c5e174500385c16c5a0c43d164121603715c3804056154391503b0e85304452 0x516e5667a71c7bae7865671648edce79071c490df650e70e490d3550e59648ed336505962caa8a7b271c2f2ab150a70a2caa0a5e15962e1a2864a58a2ca90a4af3b02ef92e50a38a1437037acaad16c72b503a831435835e0a29160596643a031433834a69271663a55039031602a32c386314328a8a086078470409d69f79d71b0846846445840885585c859608454450440409139349140f08438434828c08424c2c428a0882481c00c60840461440c3080040⟩,
  ⟨7,6,[ew6,ew7,ew8,ew9],localHints 5 0x8821c86214012108320881200041fc7e1f4070087c1ec7a1e4081e00900c771d875 0x6aeeb952106d2f7d2e0b38e0394ef93ce10c0ee33cd7668e9638d6bace9329204921d12a210791c42a16c6912c2916b5212828066390262906310020⟩,
  ⟨7,5,[ew0,ew6,ew7,ew8,ew9],localHints 5 0x951e49424c921f8912407b23c8e0108d2148c22c02228831d803224781d409 0x85a0cd6996b435176b4ab595adc2d77420a631508b18c26b433a85ada4e6242030905088c20110465288427b5ae5adcd6b16b521093192841cc6108822904300820⟩,
  ⟨0,3,[ew0,ew1,ew2],localHints 3 0x21c042140100c0220c82 0x551d8dab2798bc6ceb0a331a408⟩,
  ⟨7,4,[ew184,ew6,ew7,ew8,ew9],localHints 5 0x260872147b2007e244831e897208752588e0100200c09 0x22378e101bcea71dad1b12b52508398a320c4208400⟩,
  ⟨7,3,[ew185,ew6,ew7,ew8],localHints 4 0x1208071e8081d4850088700c8001009 0xcc5baa598837156543132010⟩,
  ⟨7,4,[ew186,ew6,ew7,ew8,ew9],localHints 4 0x21c012007e01c972140420c021d88200c751e809 0x6896ff89ee64dd8cbb61aa4298987654332100⟩,
  ⟨7,4,[ew187,ew6,ew7,ew8,ew9],localHints 5 0x2607e0048324c8501c7b020750109922c02208031e809 0x916104c809ef2380d6016b22929120e7310a418820⟩,
  ⟨7,3,[ew188,ew6,ew7,ew9],localHints 4 0x8720009020031d40421401208070087a 0x8c68ab6a9987165144132210⟩,
  ⟨7,4,[ew189,ew6,ew7,ew8,ew9],localHints 4 0x21c01200071ec082140420c021d88200c751e809 0x68763f83ee670d80cc6baa3298767653432010⟩,
  ⟨7,4,[ew0,ew1,ew7,ew8,ew9],localHints 4 0x9b26893008761d480010851ec8b00c092247a 0x67677676ee5dc767bb9a1988760540332210⟩,
  ⟨7,3,[ew0,ew1,ew3,ew9],localHints 4 0x9e1f89d0089127004214031e00922497 0xc6b6a6569938776544302210⟩,
  ⟨7,4,[ew0,ew2,ew7,ew8,ew9],localHints 4 0xa027c04244761d47e23807008830207a22409 0x5445ee8d5454ccb5459a1908706654330210⟩,
  ⟨7,3,[ew0,ew2,ew4,ew8],localHints 4 0x9e2809d010930180220c821e07a22408 0xc6b6a6869938776504300210⟩,
  ⟨7,4,[ew0,ew6,ew3,ew8,ew9],localHints 5 0x260a0008931f891268761d4870108520c8b00c7820809 0x89cc781da77bcee3b58c2ad2a12508398252046310400⟩,
  ⟨7,4,[ew0,ew6,ew4,ew8,ew9],localHints 5 0x2600426c9327c911ec761d48523801008832087800c08 0x2c505841e5595ce434ac2ad2a12428384c62902310400⟩
]

def nodesBlock1 : Array Node := #[
  ⟨7,5,[ew1,ew6,ew7,ew8,ew9],localHints 5 0x298871f4a5200a41f8972407628c8e214a20107b008a1224032288222c781e809 0x176b54b5a9adcad665988dc116b334c4510d731946258825d433a856ba4e611046a50842118c184826346107b5ae5adcd6b16b109225250631c84398c52104300820⟩,
  ⟨7,4,[ew190,ew6,ew7,ew8,ew9],localHints 4 0x260012007e24408010851ec830088200c7a1d409 0xf9893893ee36dd9c2b62aa3198987655432100⟩,
  ⟨7,4,[ew191,ew6,ew7,ew8,ew9],localHints 5 0x1f88700482200071e8081d88501083008a7224031d409 0xa789450389ef2b80d3818c2ad4a125073148218820⟩,
  ⟨7,3,[ew192,ew6,ew8,ew9],localHints 4 0x852000901c7a21c04004022080800c75 0x46c4ab6a9948176155432210⟩,
  ⟨7,4,[ew193,ew6,ew7,ew8,ew9],localHints 4 0x2608500407020760107b20c02208031e809 0x4dc42332bb430110aa41992877645432321010⟩,
  ⟨7,4,[ew1,ew2,ew7,ew8,ew9],localHints 4 0x2a4a82007b25c7e23807020032087a22c09 0xdd8c43343443bb2a12943408706655430210⟩,
  ⟨7,3,[ew1,ew2,ew7,ew5],localHints 4 0x278a92149c00c831e0062088022c07 0x7ba729528727065044030210⟩,
  ⟨7,4,[ew1,ew6,ew3,ew7,ew9],localHints 5 0x21ca900c801f8972687b1e89821404224820087820c09 0x8c4c7819a67bdce3358c22d2a12506398242906310400⟩,
  ⟨7,4,[ew1,ew6,ew7,ew5,ew9],localHints 5 0x2148726c802a07b1e89700c760108e20c780040220807 0x89d303a52f625ce3b56c22d2a4a047308452086310400⟩,
  ⟨7,5,[ew2,ew6,ew7,ew8,ew9],localHints 5 0x2b4812b00101ca41ec08248761f8042ac8b20ca2008aa22482234032387a1e009 0x97a5785adeb4e524790d8319e625c864d88bb112932cc00806f784210a6a09d4094d273092408480424610085c17b9ab5b12962d6a4a50631c84398c52102310400⟩,
  ⟨7,4,[ew194,ew6,ew7,ew8,ew9],localHints 4 0x260872089301c7b25c7e214040088300c750247a 0x5f75eed7545d1c71bb5a911287665454331210⟩,
  ⟨7,4,[ew195,ew6,ew7,ew8,ew9],localHints 4 0x2608321c80020761f8850100200c820247a 0xd5c53b5323321a510110993875654432321010⟩,
  ⟨7,4,[ew2,ew6,ew4,ew7,ew8],localHints 5 0x4832a48201c7b0209f1f8980088900c041e0851e809 0x8c4f079d27715ad3b16b2a8091810711c453148418820⟩,
  ⟨7,4,[ew2,ew6,ew7,ew5,ew8],localHints 5 0x20c01208a001ca81f8081d88b008851e0870100320009 0x89e103bc4e589ad3b00b2814a1246741c6628c8218820⟩,
  ⟨7,5,[ew6,ew3,ew7,ew8,ew9],localHints 5 0x260b221cb1214b0238af2240222c03200041f87d20ca525c79208941d4ae1e0092287a 0xcbed6e72ef7d39c8764f7c9dcec5ee799e2b5a268b35b573aad6d1ce9ce435c91180cf0138406bc0e709a202c026084b1014029d2240847114c500c022084310020⟩,
  ⟨7,4,[ew196,ew6,ew7,ew8,ew9],localHints 4 0x9821c8501c080107e20c7b008821d8031e809 0xe9c9dd9c47640890bb06aa0398987655432210⟩
]

def nodesBlock2 : Array Node := #[
  ⟨7,4,[ew6,ew197,ew7,ew8,ew9],localHints 5 0x21487004821f87b1d880010070087a020031d4b31e009 0xe989c90491ef3b9a961d6402920420e62948300820⟩,
  ⟨7,3,[ew198,ew7,ew8,ew9],localHints 4 0x8521c01208800100901c021e80800c75 0x47c41b71aa49687655432210⟩,
  ⟨7,4,[ew199,ew6,ew7,ew8,ew9],localHints 4 0x101c081d40420c02208031e809 0x45542332aa4301109941882766545432321010⟩,
  ⟨7,4,[ew6,ew3,ew4,ew8,ew9],localHints 4 0x260b421c832148e0048b25c820240800c7a 0xdd9cbb4a6419817714613003033035432210⟩,
  ⟨7,3,[ew6,ew3,ew4,ew5],localHints 4 0x2248b2749827087024060047a 0x469416911481376335432210⟩,
  ⟨7,4,[ew6,ew3,ew7,ew5,ew9],localHints 5 0x9821cb42088e22401200042448325c091d4070087a 0x821ef439a65b428604265854a2250421cc42908310820⟩,
  ⟨7,5,[ew6,ew4,ew7,ew8,ew9],localHints 5 0x260b7004b120c89010b622caf23882204852b0070087b1e40800c951d4b51e07a23409 0xb72eefdddce5e967b1e2e726c94af27be4eb5e2f7b5aa37568a54d6b9a9525ad3180ce7038027884e101a012d805300b5894229d004a007394c500c022084310020⟩,
  ⟨7,4,[ew200,ew6,ew7,ew8,ew9],localHints 4 0x98004832007a25c851f8040087b1d80320809 0x5e852872dd5cbba7545a292387665454232100⟩,
  ⟨7,4,[ew201,ew6,ew7,ew8,ew9],localHints 4 0x87200081d4850100200c820247a 0x65653a53233219510110883765654432321010⟩,
  ⟨7,4,[ew6,ew4,ew7,ew5,ew8],localHints 5 0x98004b422c8921c070087a24c85020031d48001009 0x825ef4b886610296a426605645292801cc02948300820⟩,
  ⟨7,5,[ew6,ew7,ew5,ew8,ew9],localHints 5 0x8b2148e20c872dc012c8822e4892bc81200042b47d01c022987a2e07828808024031d875 0xae2b4e7338ce73667399ac994a138548628e70ae2a2ac26584a552b4148419843208a221b86883d0e70da34296362c6a52128198603800600ca3008830906210020⟩,
  ⟨7,4,[ew202,ew6,ew7,ew8,ew9],localHints 4 0x870048224c911d47e010851ec0220c031d809 0x47842e72dd4c7b784a45212978764543212100⟩,
  ⟨7,4,[ew203,ew6,ew7,ew8,ew9],localHints 4 0x200071e8042140220c0302475 0x46546565434319618847011065654343221010⟩,
  ⟨21,7,[ew35,ew10,ew36,ew37,ew38],localHints 6 0x3601535cd6354d434c26348d1118d033cce334cc32cca324c831c203181c314c407cc330819304c02fc1d2f8bd058bc2ec1b084ba09023 0x211ad13ea59662aa683d159130a9a76075966079a520a5963c78e430a45130a8e23c74511415016215961615206015961413817c345114339e3c145114128131b75c15b29a2016412005806175146175952005003c04404c438e4844503c038020028030b1cd30b2892001c01800c01440411440c3080040⟩,
  ⟨21,6,[ew18,ew35,ew10,ew36,ew37,ew38],localHints 6 0x39415358d5350d3098d234446340e4338cc32cca3181c38ce230c19304bf2f848384bd380c8080df378dd3701f36c1d36816364210901b2ec23 0xab4ab0f3ec42b28f288a6a18f3c6a6820f3c69a720a2889a518a28370390f3e47230cf3c360388a2816210ca2832037c181f21e0c10c03c045c7113dd01c0002806d861a2990180002005865d62150060001400430c11544134913cf4504103cf2cc30e28a34c30b28a1c82091862482071861451010c3041081000⟩,
  ⟨9,3,[ew15,ew16,ew1],localHints 3 0x3a4163a0e7398c705c15 0x30ad94e7618391ea2008325a408⟩
]

def nodesBlock3 : Array Node := #[
  ⟨21,5,[ew35,ew10,ew36,ew37,ew204,ew38],localHints 5 0x368e03b41f354d3074ec37416340203accc3281c3181b3a8c12f82408423 0x2ecb31ecab2949b24c7462e841ee131ac104221056212922020e0018c0018a00106000820⟩,
  ⟨21,5,[ew205,ew35,ew10,ew36,ew37,ew38],localHints 5 0xd6354d3098d1340ce330ca070c6064c3304be084e0080dd07cda36c1d3b82431c23 0xe9d1f29c26e7b1c49aa447a1c53908118000f7000d60002580c952507310a418820⟩,
  ⟨21,5,[ew18,ew35,ew10,ew206,ew36,ew37],localHints 5 0x98d1358d534cce330ca3401930cc12f81c318483741f074163bc200842406c23 0x194610445d04b5482451029c8422448083c007340062c00129284a0e6398a418820⟩,
  ⟨21,5,[ew18,ew10,ew36,ew37,ew207,ew38],localHints 5 0x1c318ed064d534cc12f8f53d0d0120f3330ca3c82031c23374ea30c163c41b3c024 0x11aca0aac16e8b2aaaa22689162502a0a021e8714e5035801296a4a0e53144418820⟩,
  ⟨21,5,[ew23,ew18,ew10,ew36,ew37,ew38],localHints 5 0xd6354d33e4f8340f7338cc328f2080f6064163c4f0070c630cc12f8241201b2ec23 0x6bf4fcbf0fbb6cd23eaf2526424a2413e0f7344d1316251009400e0018a00106000820⟩,
  ⟨21,4,[ew23,ew17,ew18,ew36,ew38],localHints 5 0xd534cfd058fc34020330ca3d81c318c12f8fb3e82412023 0x9322c2320c23dc4131ac12d4211122020e0018a00106000820⟩,
  ⟨21,5,[ew17,ew18,ew35,ew36,ew37,ew38],localHints 5 0xc8354d3098d1070c63dcc3304be3fcfa058fe3c0d0080ce07ccc3284808c2136424 0x3a747ca709b9ec71d6831ce431c603125e971c471358258c0952507018a000c8300820⟩,
  ⟨21,5,[ew33,ew18,ew35,ew10,ew36,ew37],localHints 5 0x26344ce330ca064c3304be120dd074160841b3581f354d3090d0070c608cda40020 0x1a5654756147bd8e3ad0639c8633c60a829ee7b9a760d6a0250001cc028c8300820⟩,
  ⟨21,4,[ew208,ew35,ew10,ew36,ew37],localHints 5 0x98d1338cc3281930cc12f9013741f354d3090d00801c31823 0x9a2482a2282c1e5039a003160015401a12819cc31948310020⟩,
  ⟨21,6,[ew35,ew209,ew10,ew36,ew37,ew38],localHints 6 0x107054d6354d434c26348d1404ee419053f8c837104368db090e0080c60710307cc3064c12fc1d2f8162ed020841b36423 0xd98d9514656243513488a31914468a12114467e020d3487de18d3433cf71145c3dd0d145c2cb0cd3432cb70d3432036856da2190c50d83cf0514523cf0514572cb04d3562cb04d3551860482141860482050530434c044048f3c145000f00034038b2c134c00b0002002462892070060050440430c0040041080040⟩,
  ⟨21,5,[ew23,ew209,ew10,ew36,ew37,ew38],localHints 5 0x358d534cf93e1013ed06420f0080193d8f10581b0901c318c3304be408ee31c23 0x1cfcbf0fbbeceab90fa3dd370a128c10f43dca7354c5a929020e0300052000310020⟩,
  ⟨21,5,[ew35,ew10,ew36,ew37,ew210,ew38],localHints 5 0xd607cd534cdb074da3e4f840420090ee339063f81c3181906cc12f90208423 0x10e438cec3af7b3aaea4e7289a06439ee6b42c3056b0a921020e0014a0018a00106000820⟩,
  ⟨21,5,[ew33,ew35,ew209,ew10,ew36,ew37],localHints 5 0x26345063f81607424064c3304be4082106cd607cd534d010801c31823 0x163d4ef3bceaa4d4f3bcf28ca30801ee001ac02d4048107198a3188831884310020⟩,
  ⟨21,6,[ew35,ew10,ew36,ew37,ew207,ew38],localHints 6 0x380da398ed30819354d434c26348d1118d02ed0a374eb300cc32cca424170801c08c1f370c336c1d3c416364f006c2138824 0x53cf9ce3853cf98e38c8cc94f3e58e430f3058e230530882118f3c681f20f3c624620520814819518675e20c30875c18c3003806cf3db39a00f3c06400850821420180005c008c3025d600c3002004d55132120110033cf40e3903cf0ce38514d0c534530c0c50cb14a0c80c91861481c31831421030000c2081000⟩,
  ⟨21,5,[ew35,ew19,ew10,ew37,ew207,ew38],localHints 5 0x3b419340eb0681d3b0dd330200702307cc33c021090163c41b 0xa4a92754cf238d5150c8418cf03bd49509ce134ec3ac6a4a92841c0628c8300820⟩,
  ⟨21,5,[ew35,ew211,ew10,ew36,ew37,ew38],localHints 5 0x3b4d534c26344d0338cc328da38020064dd07c1d05821070c630cc12f82406c23 0x16ecaf0ebbacbaac4ea384b9ac5288a0e7b9ab62d495250201cc0004a0010600082000420⟩
]

def nodesBlock4 : Array Node := #[
  ⟨21,6,[ew23,ew35,ew10,ew36,ew37,ew38],localHints 6 0x15358d5350d33e50f3e0463410e338c2330cb3290d05cf63c41640cf0084e3380203681c0641f430bd36cc00750b2ecee37c24370d906c23 0xf80fb124ac82b3d2489a6a612498a682524989a724f3c99a560f3c44049124a44231124843c45625553e112010424478a7de25d11c1014926d041b49205040309a0420433cf04904b6182c96416015d55811040555541044524934104d24914100823823ce28d30b2492ca28a2492061871041c61851040c3002040⟩,
  ⟨21,5,[ew35,ew212,ew10,ew36,ew37,ew38],localHints 5 0xd6354d3098d1405063b82007cdb074da0901c3181930cc12f90206c23 0x1aeb36aea3a6d9350e8b8cd335705bd0e438cd3356c5a929020e0018a0010600082000420⟩,
  ⟨21,5,[ew23,ew35,ew10,ew213,ew37,ew38],localHints 5 0xd6068f93e0d0338cc328f6064163c41b3c0210801c07d10074ee09023 0xd3d8f5398f46cda13c8e14442183c2731cce5354c5a921404e6398a520c4110400⟩,
  ⟨21,5,[ew23,ew35,ew19,ew10,ew37,ew38],localHints 5 0xd6340ce068f93e0cc3d8193c021058f106c200701f3b8243691107423 0xe45904455046509341d12745d0220e83bd2e691844ad4941d07318a42906110400⟩,
  ⟨21,4,[ew35,ew214,ew10,ew37,ew38],localHints 5 0xd6341143381a3e41f3301d0702044cec448193c021090233c41b 0x32a8a1aa6a94a235414c799ce68d8352d49418e628c8310820⟩,
  ⟨21,5,[ew23,ew17,ew35,ew10,ew36,ew38],localHints 5 0x354d3300fe058f13ecf7454f83e42406cf60702034426084fa08c193641f 0xba2c84a1282d685425095ce4b8c4b0121e8139a26304b5080940007300052006300820⟩,
  ⟨21,6,[ew35,ew19,ew10,ew37,ew38],localHints 6 0x1535846340ce068f943cf8300cc38020318c80710d4241f30d160641b084bb090bd31c1d3c4da05823 0x48e18e32051456049f30e50e20744721e51421e45d2075142072c720938e2092dc20738e48445b54151454145148451430165a08438e18465830138e2085d62041c748050054545154551348044030038040a2cb3ca38d3002c020024020a1c720a2492001c0080100185041185103080040⟩,
  ⟨21,6,[ew215,ew35,ew10,ew37,ew38],localHints 5 0x1535918450c73181c30d063801a320200651707cbb330243001d06cdb05823 0x6a4a95618c7e1b75258941e474418c4425641d8c41d75415294216b41d29681807d2527d193682405012028d6b28d31501604020040ce740e03400e0690a47858c785ae6918c5056b111291116b50529420a6410e628463110002906310400⟩,
  ⟨21,6,[ew17,ew35,ew10,ew36,ew37,ew38],localHints 6 0x354d434c26348d1468fa3f8c6438c3308c12fcbe3c01b390e0070c80801907cdb058c0074bb3702109119364c737c23 0xd64d64f3d265034f3499252cf3cb92324f3cb86224d3498602cd3464517cf3df45118f3c821e18818734d18918c20a20974620600f00245108f70044000d0146d450d6806400090172d85c95802c00060142155061804c04114523cf4914503cf20838334d28b2cc24930b2ca2492071431851020830000c2081000⟩,
  ⟨21,5,[ew216,ew35,ew10,ew36,ew37,ew38],localHints 5 0xd6354d3098d1340ce330ca408200701f0641d0582109023 0xc891a28821e6718286a0266182b5050741cc53148320d211050741cc53148320c4110400⟩,
  ⟨21,6,[ew35,ew10,ew36,ew37,ew217],localHints 5 0x7cd5350d3470d0330cb328e0080c6070c23b4dc358c136cbf074be3001646c1b084c809023 0x80a1d2b67d10b7ca2673a277a10a73719f9825a9825e9719ad28621a0e7328e38a0673285a180c4328da37060128521158572d9351044110260a1231a127210220701e0811a4811e4701a0381205a8cc5a928380c010060290212906310020⟩,
  ⟨21,6,[ew33,ew35,ew10,ew36,ew37],localHints 6 0x26348d1338cc32cca30cdc064c12fcbe41c1b084e5308c83581f354db3501634cc00751d118d0090bd080c7318da07023 0x78e96654b49254b96478e4922877475574922977637874922872c74213222a12e030718778048055875d55849f7807403002c041b39c41b2da3003806405c02981c72985d75801c055551328549230538540f2d140f38d3052c51852452811c72812480851c5181101085000185103081000⟩,
  ⟨83,9,[ew10,ew178,ew179,ew180,ew181,ew182,ew183],localHints 6 0x41d0730cc721c4321c06f1b9304bd2e1b52d0b86c4b06b1a86913868130670c0660d84d18d2b4a9294a03d49d2649439050130f12448c0e14122484121952047c10478380443a150531483b 0x54fecfc7c4d357cefac4f4cfc0ce4c55a4d3c1ae7854c4ccc1adb7c8c3cfc0cdb5c5a3cfb869c65744d3bb49f35464c6b86946ca03cfba0965c463c6b862c6c2d32fbad2ecac63060c44c40e99ea0e94e80c49c40c43c40df9660df3cf0c49440c43040e32e40e33220c42c40df1a10c48210c41860df81f1c14c11db51e1db4dd1c15011db3cf1c141c1c13cf1db4101c16811d730c1d76991c13011d71861c12181c11861d72081c21d61c71041c11c11d55141c74d31d55141c74d31d24101c73cf1d14101c73cf1ce30c1c72cb1cd30c1c72cb1ca2081c71861c92081c71860820850821040820c0082040⟩,
  ⟨30,6,[ew48,ew49,ew50,ew51],localHints 5 0x509415013f1113e4f53c4ec45080c64e9394e0263d5374d9354d1334c93109c23 0x6aaea461efce2f7429ea30581b55ef35594685ef304e198d4a30cf24054a281e08c18c2c1ee6818028140590e729149400e028060310212906310020⟩,
  ⟨30,5,[ew40,ew48,ew49,ew50,ew51],localHints 5 0x5393e535354f14c3193952cf54d94a525405202051d46505450993209d345113350c23 0x771d2c625ce3b0e5a176c6629a2b185897273e23729ce0602d4a11950500038271890f20440008065290246b9d0631ee7358c4252b39d494a0e7084c12948310400⟩,
  ⟨30,4,[ew48,ew49,ew50,ew218,ew51],localHints 4 0x151500264f820541393193353c274c823 0xb8b8c8b8aa2898211221720650044004300210⟩
]

def nodesBlock5 : Array Node := #[
  ⟨30,4,[ew219,ew48,ew49,ew50,ew51],localHints 5 0x1404f93c4e4c64d8f54c94854820504261102711423 0x8681046798447100d6000b5000248106398a418820⟩,
  ⟨30,3,[ew48,ew49,ew50,ew220],localHints 4 0x5453e0813c09939319363d42754c23 0x79b729a92787065004300210⟩,
  ⟨30,4,[ew48,ew49,ew50,ew51,ew221],localHints 4 0x8141545404c9534f0264cc45551363d42711023 0xff8ee88dc82b1221a228980760065004300210⟩,
  ⟨30,4,[ew222,ew48,ew49,ew50,ew51],localHints 5 0x1414f93c4e4c64d8f51114008145554264c8274cc23 0x878104779c447100d6000b5000248107310a418820⟩,
  ⟨30,3,[ew48,ew49,ew223,ew51],localHints 4 0x5453e0813c09939319363d42754023 0x79b729a92787065004300210⟩,
  ⟨30,4,[ew39,ew40,ew49,ew50,ew51],localHints 4 0x5013e5613c55c205153655939318f509d3351023 0x8afa3aea3dc32aba98287306504003100210⟩,
  ⟨30,3,[ew39,ew42,ew40,ew51],localHints 4 0x5693e08139319595102750c23 0x479727872412065004300210⟩,
  ⟨30,4,[ew45,ew40,ew49,ew50,ew51],localHints 5 0x1415713e4f1484e44556c264c8c64d8f509d3351023 0x42e081bdc31a1a862d4b5212838cc00148000c2000820⟩,
  ⟨30,3,[ew45,ew46,ew40,ew50],localHints 4 0x5795d4f0264c9363d5335102750c23 0xb8a828982712065004300210⟩,
  ⟨30,4,[ew42,ew40,ew48,ew50,ew51],localHints 4 0x50139319583d55f515564f8204f02608d3250c27 0x46f43ed33cb326a694248306765403130210⟩,
  ⟨30,4,[ew46,ew40,ew48,ew50,ew51],localHints 5 0x141570c64d8f552044581334f8204f02608d3250c27 0x21a041bdc31b583599465112440ce6010a400c2300820⟩,
  ⟨30,5,[ew39,ew48,ew49,ew50,ew51],localHints 5 0x1665013e5953c4dd645593252d6358820521394d826585441114709d34515434cc23 0xbcaeae76b395b9c5614ee71d982b9c559657949762d4a173a8c611ce0b1841102208d6b24a6129432944a56b9d0631ee7358c109425a9273a0a541ce62948300820⟩,
  ⟨30,4,[ew48,ew224,ew49,ew50,ew51],localHints 4 0x1400802609d39319363d5674cc23 0x89a86969484869694848770650043002100110⟩,
  ⟨30,4,[ew48,ew49,ew50,ew51,ew225],localHints 4 0x4e4265a141111534f023080c6115334d9564c827 0xf73ceed7c70bb007a701908854756653432010⟩,
  ⟨30,4,[ew226,ew48,ew49,ew50,ew51],localHints 5 0x1401113e4f1574e4454cd3655932080265a54409c23 0x10b8202f704266852b62d484a0e1304a52106110400⟩,
  ⟨30,3,[ew48,ew227,ew50,ew51],localHints 4 0x5013e0813c09939319363d4274c823 0x79b729a92787065004300210⟩
]

def nodesBlock6 : Array Node := #[
  ⟨30,4,[ew45,ew39,ew49,ew50,ew51],localHints 5 0x16a4f93c520454e42610c44081365593209c2351533 0x32e061a1e3191c36ad8b5292340ce70980628c8310820⟩,
  ⟨30,3,[ew45,ew39,ew49,ew228],localHints 4 0x13c0995d5ad434d8205593209c2351533 0x34c387bba393876653432210⟩,
  ⟨30,4,[ew39,ew42,ew48,ew49,ew51],localHints 4 0x5655809d334e4204c94408d3650c26 0x76766767bb5a267699281207600540330210⟩,
  ⟨30,4,[ew39,ew48,ew49,ew51,ew228],localHints 5 0x204f15f5a96c4cd564c9434d826521415004409c23 0x84029784227050759d6d62d4148507318a320c4110400⟩,
  ⟨30,5,[ew45,ew48,ew49,ew50,ew51],localHints 5 0x5c1415bc444f93a4f16453139081635b826515365b5444c94a09d345214311423 0xca33108633864185816d7b5a152d0a5514ec61d532b1841102208e100b1925288c6054a21ce1294273c4a5109e283d6c6394a6b18b529273a0a541ce62948300820⟩,
  ⟨30,4,[ew48,ew229,ew49,ew50,ew51],localHints 4 0x1410802609d39319363d5674c8454cc23 0xabca8b8b6a6a8b8b6a6a990870065004300210⟩,
  ⟨30,4,[ew48,ew49,ew50,ew230,ew51],localHints 5 0x205a1404d8444f95055d3908c45099333d5564c827 0x1c8840af715a50316000420015452212839c862906310020⟩,
  ⟨30,4,[ew45,ew46,ew48,ew49,ew50],localHints 4 0x5795c09c454d8261114408d3950c20 0x76766767bb5a767699281267600540330210⟩,
  ⟨30,4,[ew45,ew48,ew49,ew50,ew228],localHints 4 0x993e1156a5ad434e420515405053209c23 0xdd12c1122187b7ba99212187665443212100⟩,
  ⟨30,5,[ew42,ew48,ew49,ew50,ew51],localHints 5 0x17550174319653d53755933535735c9395202051136099355153209d7150c4551c23 0x9ca68c66b394b12673b0c621ce331885a0cb31d29030027384cb81c002412b4a49a82800181244e46302206b9d0631ee7358c5ad434a50728cc5208430006210400⟩,
  ⟨30,4,[ew231,ew48,ew49,ew50,ew51],localHints 4 0x1404f93c59c204e4264d93209c23 0x46a41696148465654343712165654343212100⟩,
  ⟨30,4,[ew48,ew49,ew50,ew51,ew232],localHints 4 0x204d94109d3e1102611539551333d5564c823 0xee8cd886c8bb9169aa98180770065004300210⟩,
  ⟨30,4,[ew233,ew48,ew49,ew50,ew51],localHints 5 0x14057c44114c64ccf5559324e4204d82609d7650c23 0x8681106799c44100d6000b50009400e62906310020⟩,
  ⟨30,3,[ew234,ew49,ew50,ew51],localHints 4 0x5013e0813c09939319363d4274c823 0x79b729a92787065004300210⟩,
  ⟨30,4,[ew46,ew42,ew48,ew50,ew51],localHints 5 0x177114c64ccf55213610c444e4200995608c2751532 0x29a051bdc31b583599065152340ce60940520c0310820⟩,
  ⟨30,3,[ew46,ew42,ew48,ew228],localHints 4 0x1333d53657578511390995608c2751532 0x3cb375a59383756543032210⟩
]

def nodesBlock7 : Array Node := #[
  ⟨30,4,[ew42,ew48,ew49,ew51,ew228],localHints 5 0x205dd794ccf555d564c9444d826521415002711423 0x819064992f7240d600015800a48106398a320c4208020⟩,
  ⟨30,5,[ew46,ew48,ew49,ew50,ew51],localHints 5 0x5f1415d16f114c64e8f5539444e4205cd7b4d945099355204409d7a50d3352823 0x99a70e763384b928820d031dce32d774a50b5992903815b56aea0260024025ac4990160018024084610220841e37394b5b52962d6a4a50728cc5208430006210400⟩,
  ⟨30,4,[ew235,ew48,ew49,ew50,ew51],localHints 4 0x1414f93c59d3308139099361113209c23 0x57c517b715a576765454918176765454312100⟩,
  ⟨30,4,[ew48,ew49,ew50,ew236,ew51],localHints 4 0x4e5400995f080271113c114c64cd3653d564c823 0xebfb4bebdd1bcbaa1941880760055004300210⟩,
  ⟨30,4,[ew46,ew48,ew49,ew50,ew228],localHints 4 0x98445dd78319444e42051540504274cc23 0xdd86c6cbaa01900110011086765443221010⟩,
  ⟨30,5,[ew48,ew49,ew50,ew51,ew228],localHints 5 0x8026521455cd445f97c1115f5d56350d7d5c045501574e966505374cd3209c23 0x16b652dcdc982b7174a4b6292c40d022a8854106610a43194629804e10942278845104810340370c6d181800240a5a949400e00140330c6518080008030846210020⟩,
  ⟨30,4,[ew237,ew48,ew49,ew50,ew51],localHints 4 0x444f93c318f5081404e426505364c8274cc23 0x47842ed223c207b004a0023099876654323210⟩,
  ⟨30,4,[ew48,ew238,ew49,ew50,ew51],localHints 4 0x13e4f139500204d94109932114c63d4274cc23 0x7ab72aea27d7caba9787620540013002100110⟩,
  ⟨83,8,[ew178,ew239,ew179,ew180,ew181,ew182,ew183],localHints 6 0x10741cc331c8710c8706258800cd91ac6a1a46819c301998761814138c24c04c61584194382ed831518214c631883c60413178501840e4943d60012040390e97f0ec5247856 0x8ced8e8f74928f7db58ce48e8c8d088ca4928cad338c8488bcac727c838e7c8c70bca38e9078478ed49292d86e8c748792d79eb0738e90779eb2d38e9076c7b2d20892d6dbb0720760548566a86b62a4a96458456053856547a861438e6457856052056666e76262256456c56141d49056456051c565465466386165949266286165949266079e65938e65f79e65938e65d6db65920865c6db65920804105a0411da65514561751461714559551404048004d41304d49104040004d38f04030f04038e04d30c04028004b20804b2890402000400400421c20420420401c0042146040106040145042102040043042043042042040040⟩,
  ⟨40,6,[ew54,ew36,ew58,ew79,ew80],localHints 5 0x2147465c03659956504002593649916418f0b18e6343304d8c0fd8b0c82d0b98a0bc310c1844957f 0xa27c9c7dcec7fdda25c9a1f67c71cec737aa1dc781e478192981a5981d27a0ec3c5dcec5ed5a0dc380d23802538012980e43800f180cd180ce7800c0111c4105af105ce111a411164131291316a11124104e8110c8110e7104c610465110051106310400⟩,
  ⟨83,9,[ew11,ew178,ew179,ew180,ew181,ew182,ew183],localHints 6 0x10741cc331c8710c8701bc6e1b42e1b06b1a869139891a12f1312e19c301999b47c36668571346318981178610f5800dd994941404c3c4912303850489211941214c100e198150110e91e1583b 0x50ef0eabd49253df3ba8e48ea0ae8a519492a19eb950a48aa19df8b0a38ea0adf6a9938e8c7b478354928f5b748074878c7a4781f38e8dfa698073878c72c78322b38f22f180728784348352fb7086f4ae503b43843383b1ea6b85e38ea83a43843283a262e78662a59032c385e1e28c37e28431c781e7de08148109a4dd09a49c0814c109a39b0813db08138e09a3cf08164109528a0956580812810890970821c70810810950c30811160810c30951040944d30824920944d30824920913cf08238e0903cf08238e08d2cb08228a08c2cb08228a0890880821c70861040820c30851040820c3082080082040⟩,
  ⟨83,8,[ew240,ew178,ew179,ew180,ew181,ew182,ew183],localHints 6 0x10741cc331c8710c8701bc6e1b42e1b1a34bd2e025a21898104c5e1840e4943d60037629a10503c1393014124131a04841267c656799d668540e19c14c4d0443a0ec5647852 0x695d95a776186b7db5a55615a10d1069e618a1ed33690610a1ec72590555a10c70a5e5553095c93ef61832f5ee3c96093094c93c65553064d33c95493093893ec42d32c3ab3c94092c56056a75d72e762a6855c52e75559854d32c5555a674d32c5405a2738e2e74109853852cf2493051862c52493cf1860426020618e50616240428c206156204282204255506182004278205f41005f79d04240204225c0406dc0402490426c20400400421420420420401403da61834f5d73d961834f5d73d455534f4d33d65553544d33d241035138e3d141034f38e34724930a1862ca249207186041044041144041083041003041082041000⟩,
  ⟨61,7,[ew54,ew36,ew58,ew79,ew80],localHints 6 0x851d19700d96655a8651a702593648406418e63da60b1a56918d0cc136303f62c320b42e6282f4b8310c1844957f 0x60a8ca7243cf7248e260a3ca5088087213cf52181f6083c850854878728a50755d58828848368371b3cf49b6996033c348328358055748028a5835434802135031d34832084401c01443c40813901413cf08438414430408d28a14d30b0842841412090841c91442080811c71410c60840061440c3081000⟩,
  ⟨61,6,[ew54,ew113,ew36,ew58,ew79,ew80],localHints 6 0x851d1971d996655a66c47564d926418f6c191639af6b82e695ad0c18d0cc136303f62c326b1ab629aa6a57f4b83161125 0xa94a98f3e696428f2878878cf3e38a11cf1e069f1ca28769a5ca28474478f3de75c10f11329b11a6c428a5da6844c44871d34d360e3993cf64e3983cf5d659728a5d659528a4d35031d44d244311108f08039000f3c238208c08d28a34c2c22820082421c20880801c7005182102085080104003002042083080040⟩,
  ⟨78,7,[ew162,ew163,ew164,ew93,ew94],localHints 6 0xd5350d31181c340cc700cb3293e6fdbe6f5bc6edba6e5b86dc20319396d8c16d4bf0a4be059376d0c73b848090c26cc45111b209c23 0x5d7a6a4cf5965cfa684d75965c79875e75965e79a55c75964c73478e23e48e23614c73c75c15011835965c35201815964c13c119d35f79d3dc18134130164119a1c76da6581811c15c05800845145c45950805004c03c00903524503ce08034030024008a1c72ca2480801c01800c00840411440c3080040⟩,
  ⟨78,6,[ew162,ew163,ew241,ew164,ew93,ew94],localHints 6 0x354d434c46340cc32cca6dc1c6d5ca725c8515c7718c2715b909dc40813970c2970816704ee0902337044115b2 0xe8a328d34a8a138d34568580d36069f14d34520574a79d21c14a14e34d6da69b34d39a69828a64821928a6082151865c515618654514e30c08d34230c48d34228248821429308808240248515141008514000f0803ce34d04c30134d00c30128100820b289048041181005147186045143004040103082040040000⟩
]

def nodesBlock8 : Array Node := #[
  ⟨78,5,[ew163,ew241,ew164,ew242,ew93,ew94],localHints 5 0xd534dc3709010901c0a42331c484e420059c6114dc3b9cb11027 0xa2268425092ca25722083b4ed7bd0e439a769d8c2906b529284a027304a10902310400⟩,
  ⟨71,5,[ew143,ew144,ew145,ew146],localHints 6 0x775dc415db769d9761c675dd6755b96e1d474dd20a5c274416741cf3b848124467384373445111cc6e8c7 0x84838885f45181f39e7484517034436c138e64145a6433836035835c12085015955032034c444448038e3c04503c43843442c43002082402ca2442041c00c61c40461440c3080040⟩,
  ⟨71,4,[ew128,ew143,ew144,ew145,ew146],localHints 4 0x76de06e1df120c76e9ce0a4167784611045 0x25d55454c2b25454a292876545432321100⟩,
  ⟨71,4,[ew143,ew144,ew243,ew145,ew146],localHints 4 0x1db0a5c66e5ba059c2118ee31c44115ce 0x5bcbb7b7454527a22592821761154131210⟩,
  ⟨71,4,[ew244,ew143,ew144,ew145,ew146],localHints 4 0x76dc66e1df31c29058ee118446e845 0x36b625a2239265658732127656543212100⟩,
  ⟨71,4,[ew143,ew144,ew132,ew145,ew146],localHints 4 0x29119c672c16709df3b8c711443111ba 0x8c8c8c8cbb18a1159110013873653432210⟩,
  ⟨71,4,[ew245,ew143,ew144,ew145,ew146],localHints 4 0x10576de16e1d1058c70a4ee118446e845 0x3cb327a2239286743432126554343212100⟩,
  ⟨71,4,[ew143,ew144,ew145,ew122,ew146],localHints 4 0x59e3789c66e1d10a4c71184811443111ba 0xd757c75bb510a1100115918736335432210⟩,
  ⟨71,4,[ew143,ew246,ew144,ew145,ew146],localHints 4 0x76de06e8296e444059c211848114c7 0x38b88585a93858573661541132101100110⟩,
  ⟨71,4,[ew143,ew144,ew15,ew145,ew146],localHints 4 0xa446719e06e816709b911443110c7 0x6b6b6b6baa1691841713653340330032210⟩,
  ⟨71,4,[ew247,ew143,ew144,ew145,ew146],localHints 4 0x10676dd76e816790480a5b911844114c7 0x3cb3a984343187113610110554343221010⟩,
  ⟨71,4,[ew143,ew144,ew145,ew31,ew146],localHints 4 0x59e5415d70a5ba6e1c21184811443110c7 0xd959c95bb5a918115713063300335432210⟩,
  ⟨71,4,[ew143,ew144,ew142,ew145,ew146],localHints 4 0x76c160a505719b86e9c21184811443110c7 0x5bdcba51791158117713063354330032210⟩,
  ⟨71,4,[ew143,ew144,ew145,ew146,ew248],localHints 4 0xa44676dba785cb059e47990511443110c7 0xddcc74b1aa1179114813003376335432210⟩,
  ⟨78,5,[ew162,ew241,ew164,ew249,ew93,ew94],localHints 5 0x354d371dc67a0240702909db96e9b808139059c2111b279dcb11423 0xaa689425092ce457a6293b8ee8412f4bdc771dad2918b529284a027304a12902310400⟩,
  ⟨78,5,[ew162,ew250,ew163,ew164,ew93,ew94],localHints 5 0x354d3340cc329c67a41c0a4ee09dba08139059c24082411023114c7 0x2a9a24899a492891094246780de45112e4b9a769d845ac6a4a12809cc1290041846010820⟩
]

def nodesBlock9 : Array Node := #[
  ⟨78,6,[ew162,ew163,ew164,ew242,ew93,ew94],localHints 6 0xd5350d36ddb5729b607101414244f9bf6f5bc7b0dc6e9de72deb081397a82905823720ee121b27044431c27 0xe86228d34a86038d34e34d7cc31f34d38c31d28a78778728a74770e6db18d3466da38d34624964a29924918a28411818460030008d34231700d3402805495952940090004c00920821c201200040044619140f00600e34d04c30134d10c30b28a04924128a1092471080442071860440441050420840000c2081000⟩,
  ⟨78,5,[ew162,ew163,ew251,ew164,ew93,ew94],localHints 5 0xd534c1c40429090ee4f9bf6f1e9110204e416709b91202331d6711427 0x2caaaa8a9a912449495251244a318180a7a80e6800c30160525490a0e1098a12106110020⟩,
  ⟨78,6,[ew162,ew163,ew164,ew249,ew93,ew94],localHints 6 0x354d434db76f9ca6d81c7a1e2091f07bc277b8dc6e02031939304bf0a4be059ed721b2778c76e4c2714456e823 0x188a335248d8a16124984108124a041061249e34d7d57d534d79575871c15248571b6124852cb68d35a2cb14d35451914865841005248141011249734d04b2c134d10b2d511604859514505404451301200241009244040000d00e2cf38d3002c000a002202089080200007006145187180140004002042083080040⟩,
  ⟨78,5,[ew162,ew163,ew164,ew252,ew93,ew94],localHints 5 0xd534c1c40429091b908016718276e9b84e4c6304be115023b96711023 0x2cfabd2f4bdd274a8f9bdd274a3180d2f4bc2e6858c584235040940007300a00106000820⟩,
  ⟨83,9,[ew178,ew253,ew179,ew180,ew181,ew182,ew183],localHints 6 0x41d0730cc721c4321c06e12c6f7e86b1a44e1a06a131f97e0657dc1448d2448402488380e8627d8610f06004df517850039f416df30c43d1641215d1f1358a6645418d7f149307c91e0edf114c56 0x198f586be75d7fef7c698758510ed07d275d512efa590750512e39190618510e3769261838dc0d3f475d3b4c363cd74d3b4b753cd61838db6d3f461838da8d3cc41038cab33cd40d2897492aec322ae771289c092ae62f289b6f2896182aeb6d289409288aac28842b289a8928928928e34d28a28aa636db7e875d7e86db1a375d6a65d71a76181a75d76a66185a39245254105259241a341028a2a208436228a3a10842617c374309e6e07de75c0836c36836030805d91806180835c35834830934155134910834033c034008330338334308030028724b083203283243087207180100083043143103080040⟩,
  ⟨83,8,[ew178,ew253,ew179,ew254,ew180,ew181,ew182,ew183],localHints 6 0x10741cc331c8711c06e12c6f7e9f481432811a01506b1a44e1a06a131f97e06580d1f4be024b8024c201800387c4537fdfe0e9fd7f03c180131400e16c310f4590484d6285618d7f4783b7edf6 0x3fc3fd492f7cecf48f27a24b4922fae494892f0e093cf270dcb3cf22a234492d2ad88488d27d483cf2279f43cf2242072491e4cc824805248004005248007204f3ddc3004f3f1c3004b2ef24904b2ee2490482191c704822d1c7152168aaca12ac5a85a0fa459e914f3e89e714914492610994590515b15620859b8c46441411450451221004100124804100124a138e74f3dd38e84f3e079e7c925f79e74925c6da0c86816580c10d75950c55424824d05134910900823c200e3813cf08e0822c230934c2ca0890812080870822020071c10460810811450840821420041010c3081080040⟩,
  ⟨83,7,[ew178,ew253,ew254,ew255,ew181,ew182,ew183],localHints 6 0x10741cc721c4701ac690cc681a9f97e209820dc0c9a5682071b42e0086c0d8107f5fc0f06004d301400e16c310f459048635fc56150d90e03b2ee06 0xfb8fbd34efbad3d33c99c92d34cb9ec25324b7eb24f3c97ea2cf3c84c8967a654e82272253e62019883cf9419482481cb90726320b2224d37227224d37228603cf41f7d03cf81f7dd2cb78925e2cb7492412081471c52080471c34437134dc4510d30c338340f3d038e0cf0c36436896da6580c90c14170c85c10560c50c24c25115544d20910823c204e3903cf08e0822c230934c2ca0890812080870822020471c40460850840c3081081040⟩
]

def nodesGet (i : Nat) : Option Node :=
  if i < 80 then
    if i < 32 then
      if i < 16 then
        nodesBlock0[(i-0)]?
      else
        nodesBlock1[(i-16)]?
    else
      if i < 48 then
        nodesBlock2[(i-32)]?
      else
        if i < 64 then
          nodesBlock3[(i-48)]?
        else
          nodesBlock4[(i-64)]?
  else
    if i < 112 then
      if i < 96 then
        nodesBlock5[(i-80)]?
      else
        nodesBlock6[(i-96)]?
    else
      if i < 128 then
        nodesBlock7[(i-112)]?
      else
        if i < 144 then
          nodesBlock8[(i-128)]?
        else
          nodesBlock9[(i-144)]?

def fastViews : QFast.Table View := ⟨84,viewsGet⟩
def fastNodes : QFast.Table Node := ⟨151,nodesGet⟩

def aliasMap0 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,0,0,0,38,0,0,0,44,0,0,0,46,0,0,0,52,0,0,0,54,0,0,0,60,0,0,0,62,0]
def aliasMap1 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,48,0,0,0,50,0,0,0,52,0,0,0,54,0,0,0,56,0,0,0,58,0,0,0,60,0,0,0,62,0]
def aliasMap2 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,40,0,0,0,42,0,0,0,44,0,0,0,46,0,0,0,56,0,0,0,58,0,0,0,60,0,0,0,62,0]
def aliasMap3 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,0,0,42,0,0,0,43,0,0,0,18,0,0,0,19,0,0,0,58,0,0,0,59,0]
def aliasMap4 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,3,0,0,0,18,0,0,0,19,0,0,0,6,0,0,0,7,0,0,0,22,0,0,0,23,0]
def aliasMap5 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,0,0,0,11,0,0,0,42,0,0,0,43,0,0,0,14,0,0,0,15,0,0,0,46,0,0,0,47,0]
def aliasMap6 : Array Nat := #[0,0,2,0,0,0,6,0,0,0,34,0,0,0,38,0,0,0,3,0,0,0,7,0,0,0,35,0,0,0,39,0,0,0,10,0,0,0,14,0,0,0,42,0,0,0,46,0,0,0,11,0,0,0,15,0,0,0,43,0,0,0,47,0]
def aliasMap7 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,34,0,0,0,38,0,0,0,50,0,0,0,54,0,0,0,42,0,0,0,46,0,0,0,58,0,0,0,62,0]
def aliasMap8 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,33,0,0,0,35,0,0,0,25,0,0,0,27,0,0,0,57,0,0,0,59,0]
def aliasMap9 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,5,0,0,0,33,0,0,0,37,0,0,0,25,0,0,0,29,0,0,0,57,0,0,0,61,0]
def aliasMap10 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,33,0,0,0,35,0,0,0,5,0,0,0,7,0,0,0,37,0,0,0,39,0]
def aliasMap11 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,25,0,0,0,27,0,0,0,5,0,0,0,7,0,0,0,29,0,0,0,31,0]
def aliasMap12 : Array Nat := #[0,0,4,5,0,0,6,7,0,0,12,13,0,0,14,15,0,0,20,21,0,0,22,23,0,0,28,29,0,0,30,31,0,0,36,37,0,0,38,39,0,0,44,45,0,0,46,47,0,0,52,53,0,0,54,55,0,0,60,61,0,0,62,63]
def aliasMap13 : Array Nat := #[0,0,8,0,0,0,10,0,0,0,12,0,0,0,14,0,0,0,24,0,0,0,26,0,0,0,28,0,0,0,30,0,0,0,40,0,0,0,42,0,0,0,44,0,0,0,46,0,0,0,56,0,0,0,58,0,0,0,60,0,0,0,62,0]
def aliasMap14 : Array Nat := #[0,0,32,0,0,0,34,0,0,0,36,0,0,0,38,0,0,0,33,0,0,0,35,0,0,0,37,0,0,0,39,0,0,0,48,0,0,0,50,0,0,0,52,0,0,0,54,0,0,0,49,0,0,0,51,0,0,0,53,0,0,0,55,0]
def aliasMap15 : Array Nat := #[0,0,16,0,0,0,17,0,0,0,24,0,0,0,25,0,0,0,20,0,0,0,21,0,0,0,28,0,0,0,29,0,0,0,48,0,0,0,49,0,0,0,56,0,0,0,57,0,0,0,52,0,0,0,53,0,0,0,60,0,0,0,61,0]
def aliasMap16 : Array Nat := #[0,0,16,0,0,0,17,0,0,0,24,0,0,0,25,0,0,0,18,0,0,0,19,0,0,0,26,0,0,0,27,0,0,0,48,0,0,0,49,0,0,0,56,0,0,0,57,0,0,0,50,0,0,0,51,0,0,0,58,0,0,0,59,0]
def aliasMap17 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,10,0,0,0,11,0,0,0,14,0,0,0,15,0,0,0,42,0,0,0,43,0,0,0,46,0,0,0,47,0]
def aliasMap18 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,9,0,0,0,11,0,0,0,13,0,0,0,15,0,0,0,25,0,0,0,27,0,0,0,29,0,0,0,31,0]
def aliasMap19 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,2,0,3,0,4,0,5,0,6,0,7,0,16,0,17,0,18,0,19,0,20,0,21,0,22,0,23,0]
def aliasMap20 : Array Nat := #[0,48,0,49,0,50,0,51,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,52,0,53,0,54,0,55,0,56,0,57,0,58,0,59,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,60,0,61,0,62,0,63]
def aliasMap21 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,4,0,5,0,10,0,11,0,14,0,15,0,32,0,33,0,36,0,37,0,42,0,43,0,46,0,47,0]
def aliasMap22 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,3,0,0,0,5,0,0,0,7,0,0,0,33,0,0,0,35,0,0,0,37,0,0,0,39,0]
def aliasMap23 : Array Nat := #[0,0,4,0,0,0,6,0,0,0,12,0,0,0,14,0,0,0,20,0,0,0,22,0,0,0,28,0,0,0,30,0,0,0,36,0,0,0,38,0,0,0,44,0,0,0,46,0,0,0,52,0,0,0,54,0,0,0,60,0,0,0,62,0]
def aliasMap24 : Array Nat := #[0,2,0,6,0,18,0,22,0,34,0,38,0,50,0,54,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,7,0,19,0,23,0,35,0,39,0,51,0,55,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap25 : Array Nat := #[0,0,4,5,0,0,0,0,0,0,12,13,0,0,0,0,0,0,20,21,0,0,0,0,0,0,28,29,0,0,0,0,0,0,36,37,0,0,0,0,0,0,44,45,0,0,0,0,0,0,52,53,0,0,0,0,0,0,60,61,0,0,0,0]
def aliasMap26 : Array Nat := #[0,0,0,0,0,0,0,0,0,12,0,13,0,14,0,15,0,0,0,0,0,0,0,0,0,44,0,45,0,46,0,47,0,0,0,0,0,0,0,0,0,28,0,29,0,30,0,31,0,0,0,0,0,0,0,0,0,60,0,61,0,62,0,63]
def aliasMap27 : Array Nat := #[0,0,0,0,0,0,0,0,0,10,0,11,0,14,0,15,0,0,0,0,0,0,0,0,0,42,0,43,0,46,0,47,0,0,0,0,0,0,0,0,0,26,0,27,0,30,0,31,0,0,0,0,0,0,0,0,0,58,0,59,0,62,0,63]
def aliasMap28 : Array Nat := #[0,10,0,11,0,42,0,43,0,24,0,25,0,56,0,57,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,14,0,15,0,46,0,47,0,28,0,29,0,60,0,61,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap29 : Array Nat := #[0,0,0,0,0,0,0,0,0,40,0,42,0,44,0,46,0,0,0,0,0,0,0,0,0,56,0,58,0,60,0,62,0,0,0,0,0,0,0,0,0,41,0,43,0,45,0,47,0,0,0,0,0,0,0,0,0,57,0,59,0,61,0,63]
def aliasMap30 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,12,0,0,0,13,0,0,0,14,0,0,0,15,0,0,0,44,0,0,0,45,0,0,0,46,0,0,0,47,0]
def aliasMap31 : Array Nat := #[0,0,4,0,0,0,6,0,0,0,36,0,0,0,38,0,0,0,5,0,0,0,7,0,0,0,37,0,0,0,39,0,0,0,12,0,0,0,14,0,0,0,44,0,0,0,46,0,0,0,13,0,0,0,15,0,0,0,45,0,0,0,47,0]
def aliasMap32 : Array Nat := #[0,47,0,15,0,35,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,45,0,13,0,33,0,1,0,46,0,14,0,34,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,0,12,0,32,0,0]
def aliasMap33 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,33,0,0,0,40,0,0,0,41,0,0,0,38,0,0,0,39,0,0,0,46,0,0,0,47,0]
def aliasMap34 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,36,0,0,0,33,0,0,0,44,0,0,0,41,0,0,0,38,0,0,0,35,0,0,0,46,0,0,0,43,0]
def aliasMap35 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,33,0,0,0,44,0,0,0,45,0,0,0,34,0,0,0,35,0,0,0,46,0,0,0,47,0]
def aliasMap36 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,34,0,0,0,33,0,0,0,42,0,0,0,41,0,0,0,38,0,0,0,37,0,0,0,46,0,0,0,45,0]
def aliasMap37 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,32,0,0,0,33,0,0,0,42,0,0,0,43,0,0,0,36,0,0,0,37,0,0,0,46,0,0,0,47,0]
def aliasMap38 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,39,0,0,0,35,0,0,0,37,0,0,0,33,0,0,0,46,0,0,0,42,0,0,0,44,0,0,0,40,0]
def aliasMap39 : Array Nat := #[0,47,0,15,0,37,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,43,0,11,0,33,0,1,0,46,0,14,0,36,0,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,42,0,10,0,32,0,0]
def aliasMap40 : Array Nat := #[0,2,0,6,0,0,4,0,0,34,0,38,32,0,36,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,3,0,7,1,0,5,0,0,35,0,39,33,0,37,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap41 : Array Nat := #[0,1,0,5,2,0,6,0,0,9,0,13,10,0,14,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,33,0,37,34,0,38,0,0,41,0,45,42,0,46,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap42 : Array Nat := #[0,39,0,7,0,35,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,37,0,5,0,33,0,1,0,46,0,14,0,42,0,10,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,44,0,12,0,40,0,8]
def aliasMap43 : Array Nat := #[0,2,0,3,0,6,0,7,0,10,0,11,0,14,0,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,18,0,19,0,22,0,23,0,26,0,27,0,30,0,31,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0]
def aliasMap44 : Array Nat := #[0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,5,0,0,0,25,0,0,0,29,0,0,0,33,0,0,0,37,0,0,0,57,0,0,0,61,0]
def aliasMap45 : Array Nat := #[0,0,32,0,0,0,36,0,0,0,40,0,0,0,44,0,0,0,33,0,0,0,37,0,0,0,41,0,0,0,45,0,0,0,48,0,0,0,52,0,0,0,56,0,0,0,60,0,0,0,49,0,0,0,53,0,0,0,57,0,0,0,61,0]
def rootAliases : QFast.AliasTable
  | 1 => some (0, aliasMap0)
  | 2 => some (0, aliasMap1)
  | 3 => some (0, aliasMap2)
  | 4 => some (0, aliasMap0)
  | 5 => some (0, aliasMap2)
  | 6 => some (0, aliasMap1)
  | 11 => some (9, aliasMap3)
  | 13 => some (9, aliasMap4)
  | 14 => some (9, aliasMap5)
  | 15 => some (10, aliasMap6)
  | 16 => some (9, aliasMap7)
  | 17 => some (9, aliasMap7)
  | 18 => some (9, aliasMap4)
  | 19 => some (9, aliasMap5)
  | 20 => some (10, aliasMap6)
  | 22 => some (9, aliasMap8)
  | 23 => some (9, aliasMap9)
  | 24 => some (9, aliasMap8)
  | 25 => some (9, aliasMap10)
  | 26 => some (9, aliasMap11)
  | 27 => some (9, aliasMap9)
  | 28 => some (9, aliasMap10)
  | 29 => some (9, aliasMap11)
  | 32 => some (21, aliasMap12)
  | 33 => some (10, aliasMap13)
  | 34 => some (10, aliasMap14)
  | 35 => some (10, aliasMap15)
  | 36 => some (10, aliasMap16)
  | 37 => some (0, aliasMap17)
  | 38 => some (0, aliasMap18)
  | 39 => some (0, aliasMap18)
  | 41 => some (7, aliasMap19)
  | 42 => some (30, aliasMap20)
  | 43 => some (7, aliasMap21)
  | 45 => some (7, aliasMap19)
  | 46 => some (21, aliasMap12)
  | 48 => some (0, aliasMap22)
  | 50 => some (10, aliasMap23)
  | 51 => some (10, aliasMap23)
  | 52 => some (49, aliasMap24)
  | 53 => some (12, aliasMap25)
  | 54 => some (47, aliasMap26)
  | 55 => some (47, aliasMap27)
  | 56 => some (49, aliasMap28)
  | 57 => some (47, aliasMap29)
  | 58 => some (47, aliasMap26)
  | 59 => some (47, aliasMap29)
  | 60 => some (0, aliasMap30)
  | 62 => some (30, aliasMap20)
  | 63 => some (10, aliasMap31)
  | 64 => some (30, aliasMap32)
  | 65 => some (9, aliasMap33)
  | 66 => some (9, aliasMap34)
  | 67 => some (9, aliasMap35)
  | 68 => some (9, aliasMap36)
  | 69 => some (9, aliasMap37)
  | 70 => some (0, aliasMap38)
  | 72 => some (30, aliasMap39)
  | 74 => some (73, aliasMap40)
  | 75 => some (73, aliasMap40)
  | 76 => some (73, aliasMap41)
  | 77 => some (30, aliasMap42)
  | 79 => some (49, aliasMap43)
  | 80 => some (0, aliasMap44)
  | 82 => some (10, aliasMap45)
  | _ => none
end SignedProjection

namespace SignedProjection
set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_16 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 16 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_48 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 48 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_64 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 64 16 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockRoots_80 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 80 4 = true := by decide +kernel

theorem joinRoots_0_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 16 16 blockRoots_0 blockRoots_16

theorem joinRoots_0_32 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 32 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 32 16 16 blockRoots_32 blockRoots_48

theorem joinRoots_0_64 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 64 20 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 64 16 4 blockRoots_64 blockRoots_80

theorem joinRoots_1_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 64 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 32 32 joinRoots_0_0 joinRoots_0_32

theorem joinRoots_2_0 : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 84 = true :=
  @QFast.merge_blocks (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 64 20 joinRoots_1_0 joinRoots_0_64

theorem certifiedRoots : QFast.passBlock (QFast.symCheckRoot rootAliases fastViews fastNodes) 0 84 = true := joinRoots_2_0

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_12 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 12 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_36 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 36 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_60 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 60 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_84 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 84 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_108 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 108 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_132 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 132 12 = true := by decide +kernel

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem blockNodes_144 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 144 7 = true := by decide +kernel

theorem joinNodes_0_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 12 12 blockNodes_0 blockNodes_12

theorem joinNodes_0_24 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 24 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 24 12 12 blockNodes_24 blockNodes_36

theorem joinNodes_0_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 12 12 blockNodes_48 blockNodes_60

theorem joinNodes_0_72 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 72 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 72 12 12 blockNodes_72 blockNodes_84

theorem joinNodes_0_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 12 12 blockNodes_96 blockNodes_108

theorem joinNodes_0_120 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 120 24 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 120 12 12 blockNodes_120 blockNodes_132

theorem joinNodes_1_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 24 24 joinNodes_0_0 joinNodes_0_24

theorem joinNodes_1_48 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 48 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 48 24 24 joinNodes_0_48 joinNodes_0_72

theorem joinNodes_1_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 48 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 24 24 joinNodes_0_96 joinNodes_0_120

theorem joinNodes_2_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 96 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 48 48 joinNodes_1_0 joinNodes_1_48

theorem joinNodes_2_96 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 96 55 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 96 48 7 joinNodes_1_96 blockNodes_144

theorem joinNodes_3_0 : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 151 = true :=
  @QFast.merge_blocks (QFast.checkNodeAt fastViews fastNodes) 0 96 55 joinNodes_2_0 joinNodes_2_96

theorem certifiedNodes : QFast.passBlock (QFast.checkNodeAt fastViews fastNodes) 0 151 = true := joinNodes_3_0
end SignedProjection

namespace SignedProjection
def bMatches (z : Option View) : Bool :=
  match z with
  | none => false
  | some v => vg v == (0xfee8eaa8fce88080 : Word) && vk v == 10 && (vs v).toFinset == Direct64.cols.toFinset

theorem rootNegative : ¬ CoreSigned.build signedOps (0xfee8eaa8fce88080 : BitVec 64) 10 Direct64.cols.toFinset := by
  have shape : bMatches (QFast.get fastViews 83) = true := by decide +kernel
  cases ev : QFast.get fastViews 83 with
  | none => simp [ev, bMatches] at shape
  | some v =>
    have valid := QFast.symCertified rootAliases fastViews fastNodes certifiedRoots certifiedNodes ev
    simp only [ev,bMatches,Bool.and_eq_true,beq_iff_eq] at shape
    change ¬ CoreSigned.build signedOps (vg v) (vk v) (vs v).toFinset at valid
    rwa [shape.1.1,shape.1.2,shape.2] at valid
end SignedProjection
end PEqualNP.Outside.L_meta_47707_aux

open PEqualNP.Outside.L_meta_47707_aux in
theorem PEqualNP.Outside.L_meta_47707 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 4243095680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 4243095680) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) :=
  LowerSymSix.finish SignedProjection.rootNegative
