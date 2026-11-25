import PEqualNP.Outside.L_meta_529
import PEqualNP.Research.PartialIncidence

namespace PEqualNP.Research.SparseIncidence

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_529_aux

private def pay (g : Gate) : Bool :=
  g.op.casesOn (motive := fun _ => Bool) (decide (g.inputs.length = 2)) false false (fun _ => false) false

private theorem pred (g : Gate) (ops : g.op = .and ∨ g.op = .or) (fan : g.inputs.length ≤ 2)
    (v : ℕ → Bool) {a : Type} (d : a → ℕ → Bool) : ∃ T : Finset ℕ,
    T.card ≤ (if pay g then 2 else 1) ∧ ∀ u,
      g.op.eval (g.inputs.map v) = true → g.op.eval (g.inputs.map (d u)) = false →
      ∃ j ∈ T, v j = true ∧ d u j = false := by
  rcases ops with op | op
  · refine ⟨g.inputs.toFinset, ?_, ?_⟩
    · have h := List.toFinset_card_le g.inputs
      by_cases full : g.inputs.length = 2 <;> simp [pay,op,full] <;> omega
    · intro u top low
      have all : ∀ j ∈ g.inputs, v j = true := by simpa [op,GateOp.eval] using top
      have miss : ∃ j ∈ g.inputs, d u j = false := by simpa [op,GateOp.eval] using low
      obtain ⟨j,hj,off⟩ := miss
      exact ⟨j,List.mem_toFinset.mpr hj,all _ hj,off⟩
  · by_cases on : ∃ j ∈ g.inputs, v j = true
    · obtain ⟨j,hj,val⟩ := on
      refine ⟨{j}, by simp [pay,op], ?_⟩
      intro u _ low
      have all : ∀ j ∈ g.inputs, d u j = false := by simpa [op,GateOp.eval] using low
      exact ⟨j,by simp,val,all _ hj⟩
    · refine ⟨∅, by simp, ?_⟩
      intro u top _
      exact False.elim (on (by simpa [op,GateOp.eval] using top))

private def critical {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => val gs x w = true ∧ val gs (Function.update x i false) w = false

private theorem bound {n : ℕ} (gs : List Gate) (x : Fin n → Bool)
    (safe : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) (W : Finset ℕ) :
    (W.biUnion (critical gs x)).card ≤ W.card + gs.countP pay := by
  induction gs using List.reverseRecOn generalizing W with
  | nil =>
    simp only [List.countP_nil, add_zero]
    apply Finset.card_biUnion_le.trans
    calc
      ∑ j ∈ W, (critical [] x j).card ≤ ∑ _j ∈ W, 1 := by
        apply Finset.sum_le_sum
        intro j _
        by_cases h : j < n
        · apply (Finset.card_le_card (t := {⟨j,h⟩}) _).trans_eq (Finset.card_singleton _)
          intro i hi
          rcases (Finset.mem_filter.mp hi).2 with ⟨top, low⟩
          rw [val_nil, dite_eq_left h] at top low
          by_contra hne
          have ne : (⟨j,h⟩ : Fin n) ≠ i := fun e => hne (by simp [e])
          rw [Function.update_of_ne ne] at low
          exact Bool.noConfusion (top.symm.trans low)
        · simp [critical,val_nil,h]
      _ = W.card := by simp
  | append_singleton gs g ih =>
    have prev : ∀ q ∈ gs, (q.op = .and ∨ q.op = .or) ∧ q.inputs.length ≤ 2 :=
      fun q hq => safe q (by simp [hq])
    obtain ⟨T, cost, trace⟩ := pred g (safe g (by simp)).1 (safe g (by simp)).2
      (val gs x) (fun i => val gs (Function.update x i false))
    let k := n+gs.length
    have same {w : ℕ} (h : w ≠ k) : critical (gs ++ [g]) x w = critical gs x w := by
      change w ≠ n + gs.length at h
      ext i
      simp only [critical,Finset.mem_filter, Finset.mem_univ, true_and, val_snoc, ite_eq_right h]
    have new : critical (gs ++ [g]) x k ⊆ T.biUnion (critical gs x) := by
      intro i hi
      rcases (Finset.mem_filter.mp hi).2 with ⟨top, low⟩
      rw [val_snoc, ite_eq_left rfl] at top low
      obtain ⟨j,jT,ok,off⟩ := trace i top low
      exact Finset.mem_biUnion.mpr ⟨j,jT,Finset.mem_filter.mpr ⟨Finset.mem_univ _,ok,off⟩⟩
    by_cases hW : k ∈ W
    · let Z := W.erase k ∪ T
      have sub : W.biUnion (critical (gs ++ [g]) x) ⊆ Z.biUnion (critical gs x) := by
        intro i hi
        obtain ⟨j,hj,hit⟩ := Finset.mem_biUnion.mp hi
        by_cases equal : j = k
        · obtain ⟨r,rT,yes⟩ := Finset.mem_biUnion.mp (new (equal ▸ hit))
          exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_union_right _ rT,yes⟩
        · exact Finset.mem_biUnion.mpr ⟨j,Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨equal,hj⟩),same equal ▸ hit⟩
      have zw : Z.card ≤ W.card-1 + T.card := by simpa [Z,Finset.card_erase_of_mem hW] using Finset.card_union_le (W.erase k) T
      have hk : 1 ≤ W.card := Finset.card_pos.mpr ⟨_,hW⟩
      have h := (Finset.card_le_card sub).trans (ih prev Z)
      cases andGate : pay g <;> simp [andGate] at cost ⊢ <;> omega
    · have eq : W.biUnion (critical (gs ++ [g]) x) = W.biUnion (critical gs x) :=
        Finset.biUnion_congr rfl fun j hj => same (fun e => hW (e ▸ hj))
      rw [eq]
      have h := ih prev W
      simp [List.countP_append]; omega

private theorem falling (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (mono : PEqualNP.MetaComplexity.Monotone2 C) (on : C.eval (List.ofFn x) = true) :
    (Finset.univ.filter fun i => C.eval (List.ofFn (Function.update x i false)) = false).card ≤
      (C.gates.countP fun g => g.op.casesOn (motive := fun _ => Bool) (decide (g.inputs.length = 2)) false false (fun _ => false) false) + 1 := by
  change (Finset.univ.filter fun i : Fin n => PEqualNP.Outside.L_meta_529_aux.val C.gates (Function.update x i false) C.output = false).card ≤ C.gates.countP pay + 1
  have h := bound C.gates x mono {C.output}
  simpa only [Finset.singleton_biUnion, Finset.card_singleton, critical, show PEqualNP.Outside.L_meta_529_aux.val C.gates x C.output = true from on, true_and, Nat.add_comm] using h

private theorem shrink {m : ℕ} (F : Finset (Fin m) → Bool) (D : Finset (Fin m)) (hD : F D = true) :
    ∃ B ⊆ D, F B = true ∧ ∀ l ∈ B, F (B.erase l) = false := by
  classical
  have ex : ∃ k : ℕ, ∃ B : Finset (Fin m), B ⊆ D ∧ F B = true ∧ B.card = k :=
    ⟨D.card,D,Finset.Subset.refl D,hD,rfl⟩
  obtain ⟨B,bD,bOn,bc⟩ := Nat.find_spec ex
  refine ⟨B,bD,bOn,?_⟩
  intro l lB
  cases e : F (B.erase l) with
  | false => rfl
  | true =>
    have lo := Nat.find_min' ex (show ∃ H : Finset (Fin m), H ⊆ D ∧ F H = true ∧ H.card = (B.erase l).card from
      ⟨B.erase l,(Finset.erase_subset _ _).trans bD,e,rfl⟩)
    have dec := Finset.card_erase_lt_of_mem lB
    omega

private def row {n : ℕ} (B : Finset (Fin n)) (i : Fin n) := decide (i ∈ B)

private theorem drop_bit {n : ℕ} (B : Finset (Fin n)) (i : Fin n) :
    Function.update (row B) i false = row (B.erase i) := by
  funext j
  by_cases eq : j = i
  · subst j; simp [row]
  · simp [row,Function.update_of_ne eq,eq]

private theorem small_witness {n : ℕ} (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (Z : Finset (Fin n)) (hZ : C.eval (List.ofFn (row Z)) = true) :
    ∃ B ⊆ Z, C.eval (List.ofFn (row B)) = true ∧ B.card ≤ C.gates.countP pay + 1 := by
  let F (B : Finset (Fin n)) := C.eval (List.ofFn (row B))
  obtain ⟨B,sub,on,minimal⟩ := shrink F Z hZ
  refine ⟨B, sub, on, ?_⟩
  have subset : B ⊆ Finset.univ.filter (fun i => C.eval (List.ofFn (Function.update (row B) i false)) = false) := by
    intro i hi
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,by rw [drop_bit]; exact minimal i hi⟩
  exact (Finset.card_le_card subset).trans (falling n C (row B) hC on)

end PEqualNP.Research.SparseIncidence

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.SparseIncidence

/-- Each row needs negative probes only up to one more than its own binary-AND budget.
    The resulting lower bound counts gates in the shared circuit for all rows. -/
theorem PEqualNP.Research.SparseIncidence {n m d : ℕ} (S A : Fin m → Finset (Fin n))
    (incl : ∀ i, A i ⊆ S i) (codeg : ∀ u v : Fin n, u ≠ v →
      (Finset.univ.filter fun i : Fin m => u ∈ S i ∧ v ∈ S i).card ≤ d)
    (gs : List Gate) (out : Fin m → ℕ) (mono : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (k : Fin m → ℕ)
    (represent : ∀ i, ∃ D : Circuit, Monotone2 D ∧
      (D.gates.countP (fun h => h.op.casesOn (motive := fun _ => Bool) (decide (h.inputs.length = 2)) false false (fun _ => false) false)) ≤ k i ∧
      ∀ z : Fin n → Bool, D.eval (List.ofFn z) = (Circuit.mk gs (out i)).eval (List.ofFn z))
    (neg : ∀ i (B : Finset (Fin n)), Disjoint B (S i) → B.card ≤ k i + 1 →
      (Circuit.mk gs (out i)).eval (List.ofFn (fun v => decide (v ∈ B))) = false)
    (pos : ∀ i, ∀ u ∈ A i, (Circuit.mk gs (out i)).eval (List.ofFn (fun v : Fin n => decide (v = u))) = true) :
    ∑ i, ((A i).card - 1) ≤ gs.length * d := by
  apply PEqualNP.Research.PartialIncidence S A incl codeg gs out mono _ pos
  intro i
  let Z := Finset.univ \ S i
  obtain ⟨D,dx,cost,rep⟩ := represent i
  have eq : (fun v => decide (v ∉ S i)) = row Z := by funext v; simp [row,Z]
  rw [eq, ← rep]
  cases h : D.eval (List.ofFn (row Z)) with
  | false => rfl
  | true =>
    obtain ⟨B,sub,hit,small⟩ := small_witness D dx Z h
    have dis : Disjoint B (S i) := Finset.disjoint_left.mpr fun v hv hS => (Finset.mem_sdiff.mp (sub hv)).2 hS
    change D.gates.countP pay ≤ k i at cost
    have miss := neg i B dis (small.trans (Nat.add_le_add_right cost 1))
    have yes := (rep (row B)).symm.trans hit
    exact Bool.noConfusion (yes.symm.trans miss)
