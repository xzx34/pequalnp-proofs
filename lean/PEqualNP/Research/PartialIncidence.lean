import PEqualNP.Outside.L_meta_529

namespace PEqualNP.Research

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_529_aux

/-- A pair of inputs occurs together in at most `d` rows. For each row the
circuit must reject the input with precisely that row switched off and accept
the singleton inputs in `A w`. Its behavior elsewhere is unrestricted. -/
theorem PartialIncidence {n m d : ℕ} (S A : Fin m → Finset (Fin n))
    (subset : ∀ w, A w ⊆ S w)
    (load : ∀ u v : Fin n, u ≠ v →
      (Finset.univ.filter fun w : Fin m => u ∈ S w ∧ v ∈ S w).card ≤ d)
    (gates : List Gate) (out : Fin m → ℕ)
    (basis : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (negative : ∀ w, (Circuit.mk gates (out w)).eval
      (List.ofFn (fun v => decide (v ∉ S w))) = false)
    (positive : ∀ w, ∀ u ∈ A w, (Circuit.mk gates (out w)).eval
      (List.ofFn (fun v : Fin n => decide (v = u))) = true) :
    ∑ w, ((A w).card - 1) ≤ gates.length * d := by
  classical
  choose label inv budget using fun w => main_inv (S w) gates basis
  have row_bound (w : Fin m) : (A w).card - 1 ≤ (D (S w) gates).card := by
    have merged : ((A w).image (label w)).card ≤ 1 := by
      rw [Finset.card_le_one]
      intro a ha b hb
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hb
      exact (inv w (out w) u v (negative w) (positive w u hu) (positive w v hv)).2
    have all_labels : ((S w).image (label w)).card ≤ (S w \ A w).card + 1 := by
      calc
        _ = (((S w \ A w).image (label w)) ∪ ((A w).image (label w))).card := by
          rw [← Finset.image_union, Finset.sdiff_union_of_subset (subset w)]
        _ ≤ ((S w \ A w).image (label w)).card + ((A w).image (label w)).card :=
          Finset.card_union_le _ _
        _ ≤ _ := Nat.add_le_add Finset.card_image_le merged
    have partition := Finset.card_sdiff_add_card_eq_card (subset w)
    have bound := budget w
    omega
  have wire_bound (i : ℕ) : (Finset.univ.filter fun w : Fin m => i ∈ D (S w) gates).card ≤ d := by
    by_cases used : ∃ w, i ∈ D (S w) gates
    · obtain ⟨w, hw⟩ := used
      obtain ⟨_, _, u, v, huv, hu, hv⟩ := Finset.mem_filter.mp hw
      apply le_trans (Finset.card_le_card ?_) (load u v huv)
      intro t ht
      have hz := (Finset.mem_filter.mp (Finset.mem_filter.mp ht).2).2.1
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ t,
        (inv t i u u hz hu hu).1, (inv t i v v hz hv hv).1⟩
    · have none : (Finset.univ.filter fun w : Fin m => i ∈ D (S w) gates) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact used ⟨w, (Finset.mem_filter.mp hw).2⟩
      simp [none]
  let wires := Finset.Ico n (n + gates.length)
  calc
    ∑ w, ((A w).card - 1) ≤ ∑ w, (D (S w) gates).card := Finset.sum_le_sum fun w _ => row_bound w
    _ = ∑ w : Fin m, ∑ i ∈ wires, if i ∈ D (S w) gates then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      rw [Finset.sum_boole]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun hi => ⟨(Finset.mem_filter.mp hi).1, hi⟩, And.right⟩
    _ = ∑ i ∈ wires, ∑ w : Fin m, if i ∈ D (S w) gates then 1 else 0 := Finset.sum_comm
    _ ≤ ∑ _i ∈ wires, d := by
      apply Finset.sum_le_sum
      intro i _
      rw [← Finset.card_filter]
      exact wire_bound i
    _ = gates.length * d := by simp [wires]

end PEqualNP.Research
