import Mathlib
import PEqualNP.Defs

namespace LMeta143

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity

def target (x : Fin 3 → Bool) : Bool := (x 0 && x 1) || (x 1 && x 2)

def flip (i : Fin 3) (x : Fin 3 → Bool) : Fin 3 → Bool :=
  fun j => if j = i then !(x j) else x j

def good : Circuit := ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩

def read3 (x : Fin 3 → Bool) (j : ℕ) : Bool :=
  if j = 0 then x 0 else if j = 1 then x 1 else if j = 2 then x 2 else false

lemma ofFn_read (x : Fin 3 → Bool) (j : ℕ) :
    (List.ofFn x).getD j false = read3 x j := by
  unfold read3
  by_cases h0 : j = 0
  · simp [h0]
  by_cases h1 : j = 1
  · simp [h1]
  by_cases h2 : j = 2
  · simp [h2]
  · have hj : 3 ≤ j := by omega
    simp [h0, h1, h2, List.getD_eq_default, List.length_ofFn, hj]

lemma flip_read (x : Fin 3 → Bool) (i : Fin 3) {j : ℕ} (hj : j ≠ i.val) :
    read3 (flip i x) j = read3 x j := by
  unfold read3 flip
  by_cases h0 : j = 0
  · have hi : (0 : Fin 3) ≠ i := by
      intro h
      exact hj (h ▸ h0)
    simp [h0, hi]
  by_cases h1 : j = 1
  · have hi : (1 : Fin 3) ≠ i := by
      intro h
      exact hj (h ▸ h1)
    simp [h0, h1, hi]
  by_cases h2 : j = 2
  · have hi : (2 : Fin 3) ≠ i := by
      intro h
      exact hj (h ▸ h2)
    simp [h0, h1, h2, hi]
  · simp [h0, h1, h2]

lemma map_read_stable (ins : List ℕ) (i : Fin 3) (x : Fin 3 → Bool) (h : i.val ∉ ins) :
    ins.map (fun j => read3 (flip i x) j) = ins.map (fun j => read3 x j) := by
  induction ins with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h ⊢
    rw [List.cons.injEq]
    exact ⟨flip_read x i (Ne.symm h.1), ih h.2⟩

lemma map_ofFn_stable (ins : List ℕ) (i : Fin 3) (x : Fin 3 → Bool) (h : i.val ∉ ins) :
    ins.map (fun j => (List.ofFn (flip i x)).getD j false) =
      ins.map (fun j => (List.ofFn x).getD j false) := by
  simp only [ofFn_read]
  exact map_read_stable ins i x h

lemma exists_fin3_ne (o : ℕ) : ∃ i : Fin 3, i.val ≠ o := by
  by_cases h : o = 0
  · exact ⟨1, by simp [h]⟩
  · exact ⟨0, Ne.symm h⟩

lemma exists_fin3_not_mem (l : List ℕ) (hl : l.length ≤ 2) : ∃ i : Fin 3, i.val ∉ l := by
  cases l with
  | nil => exact ⟨0, by simp⟩
  | cons a l =>
    cases l with
    | nil =>
      if ha : a = 0 then exact ⟨1, by simp [ha]⟩
      else
        exact ⟨0, by
          intro h
          simp only [List.mem_singleton] at h
          exact ha h.symm⟩
    | cons b l =>
      cases l with
      | nil =>
        if h0 : 0 ≠ a ∧ 0 ≠ b then
          exact ⟨0, by simp [h0]⟩
        else if h1 : 1 ≠ a ∧ 1 ≠ b then
          exact ⟨1, by simp [h1]⟩
        else
          refine ⟨2, ?_⟩
          intro hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          have hor0 : 0 = a ∨ 0 = b := by
            by_contra hn
            exact h0 ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
          have hor1 : 1 = a ∨ 1 = b := by
            by_contra hn
            exact h1 ⟨fun h => hn (Or.inl h), fun h => hn (Or.inr h)⟩
          rcases hmem with rfl | rfl
          · rcases hor0 with h0a | h0b
            · cases h0a
            · rcases hor1 with h1a | h1b
              · cases h1a
              · cases h1b
                cases h0b
          · rcases hor0 with h0a | h0b
            · rcases hor1 with h1a | h1b
              · cases h1a
                cases h0a
              · cases h1b
            · cases h0b
      | cons _ _ =>
        simp at hl

lemma target_moves (i : Fin 3) : ∃ x : Fin 3 → Bool, target (flip i x) ≠ target x := by
  fin_cases i
  · exact ⟨![false, true, false], by decide⟩
  · exact ⟨![true, false, false], by decide⟩
  · exact ⟨![false, true, false], by decide⟩

lemma fanin_len {D : Circuit} (hF : FanInTwo D) {g : Gate} (hg : g ∈ D.gates) :
    g.inputs.length ≤ 2 :=
  (hF g hg).2

def notHead (ins : List ℕ) : List ℕ :=
  match ins with
  | [] => []
  | a :: _ => if a < 3 then [a] else []

def relOf (g0ins g1ins : List ℕ) : List ℕ :=
  g1ins.flatMap fun j => if j = 3 then notHead g0ins else if j < 3 then [j] else []

lemma notHead_length (ins : List ℕ) : (notHead ins).length ≤ 1 := by
  cases ins with
  | nil => simp [notHead]
  | cons _ _ =>
    simp only [notHead]
    split_ifs <;> simp

lemma piece_length (g0ins : List ℕ) (j : ℕ) :
    (if j = 3 then notHead g0ins else if j < 3 then [j] else []).length ≤ 1 := by
  by_cases h3 : j = 3
  · simp [h3, notHead_length]
  · by_cases hj : j < 3
    · simp [h3, hj]
    · simp [h3, hj]

lemma rel_length_le (g0ins g1ins : List ℕ) :
    (relOf g0ins g1ins).length ≤ g1ins.length := by
  unfold relOf
  induction g1ins with
  | nil => simp
  | cons a as ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have ha := piece_length g0ins a
    omega

lemma rel_length (g0ins g1ins : List ℕ) (h1 : g1ins.length ≤ 2) :
    (relOf g0ins g1ins).length ≤ 2 := by
  have := rel_length_le g0ins g1ins
  omega

lemma append1_read (x : Fin 3 → Bool) (b0 : Bool) (j : ℕ) :
    (List.ofFn x ++ [b0]).getD j false = if j = 3 then b0 else read3 x j := by
  by_cases h0 : j = 0
  · simp [h0, read3]
  by_cases h1 : j = 1
  · simp [h1, read3]
  by_cases h2 : j = 2
  · simp [h2, read3]
  by_cases h3 : j = 3
  · simp [h3, read3]
  · have hj : 4 ≤ j := by omega
    simp [h0, h1, h2, h3, read3, List.getD_eq_default, List.length_append, List.length_ofFn, hj]

lemma wires_nil (x : Fin 3 → Bool) (o : ℕ) :
    circuitFun 3 ⟨[], o⟩ x = read3 x o := by
  simp [circuitFun, Circuit.eval, Circuit.wires]
  exact ofFn_read x o

def gateVal (g : Gate) (x : Fin 3 → Bool) : Bool :=
  g.op.eval (g.inputs.map fun j => (List.ofFn x).getD j false)

lemma map_getD_read (ins : List ℕ) (x : Fin 3 → Bool) :
    ins.map (fun j => (List.ofFn x).getD j false) = ins.map (read3 x) := by
  induction ins with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨ofFn_read x a, ih⟩

lemma map_append1 (ins : List ℕ) (x : Fin 3 → Bool) (b0 : Bool) :
    ins.map (fun j => (List.ofFn x ++ [b0]).getD j false) =
      ins.map (fun j => if j = 3 then b0 else read3 x j) := by
  induction ins with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨append1_read x b0 a, ih⟩

lemma gateVal_read (g : Gate) (x : Fin 3 → Bool) :
    gateVal g x = g.op.eval (g.inputs.map (read3 x)) := by
  simp only [gateVal]
  exact congrArg g.op.eval (map_getD_read g.inputs x)

lemma wires_one (g : Gate) (o : ℕ) (x : Fin 3 → Bool) :
    circuitFun 3 ⟨[g], o⟩ x =
      (List.ofFn x ++ [gateVal g x]).getD o false := by
  simp [circuitFun, Circuit.eval, Circuit.wires, gateVal]

def b0val (g0 : Gate) (x : Fin 3 → Bool) : Bool := gateVal g0 x

lemma wires_two (g0 g1 : Gate) (o : ℕ) (x : Fin 3 → Bool) :
    circuitFun 3 ⟨[g0, g1], o⟩ x =
      (List.ofFn x ++ [b0val g0 x] ++
        [g1.op.eval (g1.inputs.map fun j => (List.ofFn x ++ [b0val g0 x]).getD j false)]).getD
        o false := by
  simp [circuitFun, Circuit.eval, Circuit.wires, b0val, gateVal]

lemma read_out_one (g : Gate) (o : ℕ) (x : Fin 3 → Bool) (ho : o ≠ 3) :
    circuitFun 3 ⟨[g], o⟩ x = read3 x o := by
  rw [wires_one]
  by_cases hlt : o < 3
  · rw [List.getD_append _ _ false o (by simpa [List.length_ofFn] using hlt), ofFn_read]
  · have hle : 3 ≤ o := Nat.not_lt.mp hlt
    rcases lt_or_eq_of_le hle with hlt3 | heq
    · have hge : 4 ≤ o := Nat.succ_le_of_lt hlt3
      have h0 : o ≠ 0 := by omega
      have h1 : o ≠ 1 := by omega
      have h2 : o ≠ 2 := by omega
      rw [List.getD_append_right _ _ false o (by simpa [List.length_ofFn] using hle)]
      rw [List.getD_eq_default]
      · simp [read3, h0, h1, h2]
      · simp
        omega
    · exact (ho heq.symm).elim

lemma read_out_two_ne (g0 g1 : Gate) (o : ℕ) (x : Fin 3 → Bool) (h3 : o ≠ 3) (h4 : o ≠ 4) :
    circuitFun 3 ⟨[g0, g1], o⟩ x = read3 x o := by
  rw [wires_two]
  by_cases hlt : o < 3
  · have hmid : o < (List.ofFn x ++ [b0val g0 x]).length := by
      simp [List.length_ofFn, List.length_append]
      omega
    rw [List.getD_append _ _ false o hmid]
    rw [List.getD_append _ _ false o (by simpa [List.length_ofFn] using hlt), ofFn_read]
  · have hle4 : 4 ≤ o := by
      have hle : 3 ≤ o := Nat.not_lt.mp hlt
      rcases lt_or_eq_of_le hle with hlt3 | heq
      · exact Nat.succ_le_of_lt hlt3
      · exact (h3 heq.symm).elim
    have hge : 5 ≤ o := by
      rcases lt_or_eq_of_le hle4 with hlt4 | heq
      · exact Nat.succ_le_of_lt hlt4
      · exact (h4 heq.symm).elim
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    rw [List.getD_append_right _ _ false o]
    · rw [List.getD_eq_default]
      · simp [read3, h0, h1, h2]
      · simp
        omega
    · simp [List.length_ofFn, List.length_append]
      omega

lemma out_is_gate (g : Gate) (x : Fin 3 → Bool) :
    circuitFun 3 ⟨[g], 3⟩ x = gateVal g x := by
  rw [wires_one]
  rw [List.getD_append_right _ _ false 3 (by simp [List.length_ofFn])]
  simp

lemma out_is_b0 (g0 g1 : Gate) (x : Fin 3 → Bool) :
    circuitFun 3 ⟨[g0, g1], 3⟩ x = b0val g0 x := by
  rw [wires_two]
  have hmid : 3 < (List.ofFn x ++ [b0val g0 x]).length := by
    simp [List.length_ofFn]
  rw [List.getD_append _ _ false 3 hmid]
  rw [List.getD_append_right _ _ false 3 (by simp [List.length_ofFn])]
  simp [b0val]

lemma out_is_b1 (g0 g1 : Gate) (x : Fin 3 → Bool) :
    circuitFun 3 ⟨[g0, g1], 4⟩ x =
      g1.op.eval (g1.inputs.map fun j => if j = 3 then b0val g0 x else read3 x j) := by
  rw [wires_two]
  have hlen : (List.ofFn x ++ [b0val g0 x]).length = 4 := by simp [List.length_ofFn]
  rw [List.getD_append_right _ _ false 4 (by simpa [hlen] using (le_refl 4))]
  simp [hlen]
  exact congrArg g1.op.eval (map_append1 g1.inputs x (b0val g0 x))

lemma good_fan : FanInTwo good := by
  intro g hg
  simp only [good, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact ⟨by simp [Set.mem_insert_iff, Set.mem_singleton_iff], by simp⟩
  · exact ⟨by simp [Set.mem_insert_iff, Set.mem_singleton_iff], by simp⟩

lemma good_fun : circuitFun 3 good = target := by
  funext x
  rw [show good = ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.and, [1, 3]⟩], 4⟩ from rfl, out_is_b1]
  simp [b0val, gateVal, read3, GateOp.eval, target]
  rw [Bool.and_or_distrib_left, Bool.and_comm (x 1) (x 0)]

lemma irrelevant_le_one (D : Circuit) (_hF : FanInTwo D) (hs : D.size ≤ 1) :
    ∃ i : Fin 3, ∀ x, circuitFun 3 D (flip i x) = circuitFun 3 D x := by
  cases D with
  | mk gates output =>
    cases gates with
    | nil =>
      obtain ⟨i, hi⟩ := exists_fin3_ne output
      refine ⟨i, fun x => ?_⟩
      simp [Circuit.size] at hs
      rw [wires_nil, wires_nil, flip_read x i (Ne.symm hi)]
    | cons g gs =>
      cases gs with
      | cons _ _ =>
        simp [Circuit.size] at hs
      | nil =>
        by_cases ho : output = 3
        · have hin : g.inputs.length ≤ 2 := by
            simpa [Circuit.size] using fanin_len _hF (by simp)
          obtain ⟨i, hi⟩ := exists_fin3_not_mem g.inputs hin
          refine ⟨i, fun x => ?_⟩
          rw [ho, out_is_gate, out_is_gate]
          simp only [gateVal]
          exact congrArg g.op.eval (map_ofFn_stable g.inputs i x hi)
        · obtain ⟨i, hi⟩ := exists_fin3_ne output
          refine ⟨i, fun x => ?_⟩
          rw [read_out_one g output x ho, read_out_one g output (flip i x) ho,
            flip_read x i (Ne.symm hi)]

lemma ge_two (D : Circuit) (hF : FanInTwo D) (hf : circuitFun 3 D = target) : 2 ≤ D.size := by
  by_contra hlt
  have hs : D.size ≤ 1 := by omega
  obtain ⟨i, hi⟩ := irrelevant_le_one D hF hs
  obtain ⟨x, hx⟩ := target_moves i
  have : target (flip i x) = target x := by
    rw [← congrFun hf (flip i x), ← congrFun hf x]
    exact hi x
  exact hx this

lemma not_eval (ins : List ℕ) (x : Fin 3 → Bool) :
    GateOp.not.eval (ins.map (read3 x)) =
      match ins with
      | [] => true
      | a :: _ => !(read3 x a) := by
  cases ins with
  | nil => simp [GateOp.eval]
  | cons a _ => simp [GateOp.eval]

lemma head_ne {g0ins g1ins : List ℕ} {i : Fin 3} (h3 : 3 ∈ g1ins)
    (hi : i.val ∉ relOf g0ins g1ins) {a : ℕ} {as : List ℕ} (hins : g0ins = a :: as) :
    a ≠ i.val := by
  subst hins
  by_cases ha : a < 3
  · intro heq
    apply hi
    unfold relOf notHead
    rw [List.mem_flatMap]
    refine ⟨3, h3, ?_⟩
    simp [ha, heq]
  · have := i.isLt
    omega

lemma b0_stable (g0 : Gate) (g1ins : List ℕ) (i : Fin 3) (x : Fin 3 → Bool)
    (hop : g0.op = GateOp.not) (h3 : 3 ∈ g1ins) (hi : i.val ∉ relOf g0.inputs g1ins) :
    gateVal g0 (flip i x) = gateVal g0 x := by
  rw [gateVal_read, gateVal_read, hop]
  cases hins : g0.inputs with
  | nil => simp [not_eval, hins]
  | cons a as =>
    have hne := head_ne h3 hi hins
    simp [GateOp.eval, flip_read x i hne]

lemma lookup_stable (g0 : Gate) (g1ins : List ℕ) (i : Fin 3) (x : Fin 3 → Bool)
    (hop : g0.op = GateOp.not) (hi : i.val ∉ relOf g0.inputs g1ins) {j : ℕ} (hj : j ∈ g1ins) :
    (if j = 3 then gateVal g0 (flip i x) else read3 (flip i x) j) =
      if j = 3 then gateVal g0 x else read3 x j := by
  by_cases h3 : j = 3
  · have hmem : 3 ∈ g1ins := by simpa [h3] using hj
    simp [h3, b0_stable g0 g1ins i x hop hmem hi]
  · have hne : j ≠ i.val := by
      by_cases hj3 : j < 3
      · intro heq
        apply hi
        unfold relOf
        rw [List.mem_flatMap]
        refine ⟨j, hj, ?_⟩
        subst heq
        rw [if_neg h3, if_pos hj3]
        simp
      · have := i.isLt
        omega
    simp [h3, flip_read x i hne]

lemma map_lookup_stable (g0 : Gate) (i : Fin 3) (x : Fin 3 → Bool) (hop : g0.op = GateOp.not)
    (ins : List ℕ) (hi : i.val ∉ relOf g0.inputs ins) :
    ins.map (fun j => if j = 3 then gateVal g0 (flip i x) else read3 (flip i x) j) =
      ins.map (fun j => if j = 3 then gateVal g0 x else read3 x j) := by
  induction ins with
  | nil => simp
  | cons a as ih =>
    have hi_tail : i.val ∉ relOf g0.inputs as := by
      intro h
      apply hi
      unfold relOf
      simp only [List.flatMap_cons, List.mem_append]
      exact Or.inr h
    simp only [List.map_cons, List.cons.injEq]
    exact ⟨lookup_stable g0 (a :: as) i x hop hi (by simp), ih hi_tail⟩

lemma irrelevant_output_ne_four (g0 g1 : Gate) (o : ℕ) (ho : o ≠ 4)
    (hlen0 : g0.inputs.length ≤ 2) :
    ∃ i : Fin 3, ∀ x, circuitFun 3 ⟨[g0, g1], o⟩ (flip i x) = circuitFun 3 ⟨[g0, g1], o⟩ x := by
  by_cases h3 : o = 3
  · obtain ⟨i, hi⟩ := exists_fin3_not_mem g0.inputs hlen0
    refine ⟨i, fun x => ?_⟩
    rw [h3, out_is_b0, out_is_b0, b0val, b0val]
    simp only [gateVal]
    exact congrArg g0.op.eval (map_ofFn_stable g0.inputs i x hi)
  · obtain ⟨i, hi⟩ := exists_fin3_ne o
    refine ⟨i, fun x => ?_⟩
    rw [read_out_two_ne g0 g1 o (flip i x) h3 ho, read_out_two_ne g0 g1 o x h3 ho,
      flip_read x i (Ne.symm hi)]

lemma irrelevant_g0_not (g0 g1 : Gate) (hop : g0.op = GateOp.not) (hlen1 : g1.inputs.length ≤ 2) :
    ∃ i : Fin 3, ∀ x, circuitFun 3 ⟨[g0, g1], 4⟩ (flip i x) = circuitFun 3 ⟨[g0, g1], 4⟩ x := by
  obtain ⟨i, hi⟩ := exists_fin3_not_mem (relOf g0.inputs g1.inputs) (rel_length _ _ hlen1)
  refine ⟨i, fun x => ?_⟩
  rw [out_is_b1, out_is_b1]
  simp only [b0val]
  exact congrArg g1.op.eval (map_lookup_stable g0 i x hop g1.inputs hi)

lemma g1_head_stable (g0 g1 : Gate) (hop : g1.op = GateOp.not) (hlen0 : g0.inputs.length ≤ 2) :
    ∃ vars : List ℕ, vars.length ≤ 2 ∧
      ∀ i : Fin 3, i.val ∉ vars → ∀ x,
        (match g1.inputs with
          | [] => true
          | a :: _ =>
            !(if a = 3 then gateVal g0 (flip i x) else read3 (flip i x) a)) =
          match g1.inputs with
          | [] => true
          | a :: _ => !(if a = 3 then gateVal g0 x else read3 x a) := by
  cases hins : g1.inputs with
  | nil =>
    exact ⟨[], by simp, fun _ _ _ => by simp [hins]⟩
  | cons a as =>
    by_cases ha : a = 3
    · refine ⟨g0.inputs, hlen0, ?_⟩
      intro i hi x
      simp only [hins, ha]
      exact congrArg (fun b => !b) (congrArg g0.op.eval (map_ofFn_stable g0.inputs i x hi))
    · refine ⟨if a < 3 then [a] else [], by split_ifs <;> simp, ?_⟩
      intro i hi x
      have hne : a ≠ i.val := by
        by_cases hlt : a < 3
        · intro heq
          apply hi
          simp [hlt, heq]
        · have := i.isLt
          omega
      simp [hins, ha, flip_read x i hne]

lemma irrelevant_g1_not (g0 g1 : Gate) (hop : g1.op = GateOp.not) (hlen0 : g0.inputs.length ≤ 2) :
    ∃ i : Fin 3, ∀ x, circuitFun 3 ⟨[g0, g1], 4⟩ (flip i x) = circuitFun 3 ⟨[g0, g1], 4⟩ x := by
  obtain ⟨vars, hv, hstab⟩ := g1_head_stable g0 g1 hop hlen0
  obtain ⟨i, hi⟩ := exists_fin3_not_mem vars hv
  refine ⟨i, fun x => ?_⟩
  rw [out_is_b1, out_is_b1, hop]
  simp only [b0val, GateOp.eval]
  cases hins : g1.inputs with
  | nil =>
    simp [hins]
  | cons a as =>
    simp [hins, List.headD]
    have hs := hstab i hi x
    simp [hins] at hs
    exact hs

lemma has_not_false (D : Circuit) (hF : FanInTwo D) (hsize : D.size = 2)
    (hnot : ∃ g ∈ D.gates, g.op = GateOp.not) (hf : circuitFun 3 D = target) : False := by
  cases D with
  | mk gates output =>
    cases gates with
    | nil => simp [Circuit.size] at hsize
    | cons g0 gs =>
      cases gs with
      | nil => simp [Circuit.size] at hsize
      | cons g1 gs =>
        cases gs with
        | cons _ _ => simp [Circuit.size] at hsize
        | nil =>
          have hlen0 : g0.inputs.length ≤ 2 := fanin_len hF (by simp)
          have hlen1 : g1.inputs.length ≤ 2 := fanin_len hF (by simp)
          have hirr : ∃ i : Fin 3,
              ∀ x, circuitFun 3 ⟨[g0, g1], output⟩ (flip i x) =
                circuitFun 3 ⟨[g0, g1], output⟩ x := by
            by_cases ho : output = 4
            · subst ho
              obtain ⟨g, hgmem, hop⟩ := hnot
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hgmem
              cases hgmem with
              | inl h =>
                exact irrelevant_g0_not g0 g1 (h ▸ hop) hlen1
              | inr h =>
                exact irrelevant_g1_not g0 g1 (h ▸ hop) hlen0
            · exact irrelevant_output_ne_four g0 g1 output ho hlen0
          obtain ⟨i, hi⟩ := hirr
          obtain ⟨x, hx⟩ := target_moves i
          have : target (flip i x) = target x := by
            have hfun := congrFun hf
            rw [← hfun (flip i x), ← hfun x]
            exact hi x
          exact hx this

end LMeta143

theorem PEqualNP.Outside.L_meta_143 :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.IsMinimalCircuit 3 C →
        PEqualNP.MetaComplexity.circuitFun 3 C =
          (fun x : Fin 3 → Bool => (x 0 && x 1) || (x 1 && x 2)) →
          C.size = 2 ∧ ∀ g ∈ C.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not := by
  intro C hmin hf
  have hF : PEqualNP.MetaComplexity.FanInTwo C := hmin.1
  have hle : C.size ≤ 2 := by
    have hcmp := hmin.2 LMeta143.good LMeta143.good_fan (by
      rw [LMeta143.good_fun, hf]
      rfl)
    simpa [LMeta143.good, PEqualNP.CircuitLowerBounds.Circuit.size] using hcmp
  have hge : 2 ≤ C.size := LMeta143.ge_two C hF hf
  have hsize : C.size = 2 := by omega
  refine ⟨hsize, ?_⟩
  intro g hg hop
  exact LMeta143.has_not_false C hF hsize ⟨g, hg, hop⟩ hf
