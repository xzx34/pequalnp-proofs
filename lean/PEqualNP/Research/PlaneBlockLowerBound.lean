import PEqualNP.Outside.L_meta_529
import PEqualNP.MetaComplexity.Helpers.PermInputs

namespace PEqualNP.Research.PlaneBlockLowerBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev V := Fin 13
abbrev inc (p w : V) := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
abbrev points (w : V) : Finset (Fin 26) :=
  ({w,w+1,w+3,w+9} : Finset V).image (Fin.castAdd 13)

def tri (v : V) (i : Fin 6) : Finset V :=
  {v, v + Fin.ofNat 13 (2*i.val+1), v + Fin.ofNat 13 (2*i.val+2)}

set_option maxRecDepth 10000 in
private theorem triangleFacts :
    (∀ (v : V) (i : Fin 6), v ∈ tri v i ∧ (tri v i).card = 3 ∧ ¬∃ p, ∀ w ∈ tri v i, inc p w) ∧
    ∀ (v : V) (i k : Fin 6), i ≠ k → (tri v i ∩ tri v k) = {v} := by decide +kernel

private theorem countBlocks {s j : ℕ} (single : Fin s → V) (inj : Function.Injective single)
    (B : Fin j → Finset V) (small : ∀ i, 2 ≤ (B i).card ∧ (B i).card ≤ 3)
    (cover : ∀ (v : V) (T : Finset V), (∀ z, single z ≠ v) → v ∈ T → T.card = 3 →
      (¬∃ p, ∀ w ∈ T, inc p w) → ∃ i, v ∈ B i ∧ B i ⊆ T) : 2*(13-s) ≤ j := by
  classical
  let missing := Finset.univ \ Finset.univ.image single
  have countMissing : missing.card = 13 - s := by
    simp [missing,Finset.card_sdiff_of_subset,Finset.card_image_of_injective _ inj]
  have six (v : V) (hv : v ∈ missing) : 6 ≤ (Finset.univ.filter fun i => v ∈ B i).card := by
    have absent : ∀ z, single z ≠ v := by simpa [missing] using hv
    choose f member sub using fun i : Fin 6 => cover v (tri v i) absent
      (triangleFacts.1 v i).1 (triangleFacts.1 v i).2.1 (triangleFacts.1 v i).2.2
    have fi : Function.Injective f := by
      intro a b eq
      by_contra ne
      have incl : B (f a) ⊆ {v} := by
        rw [← triangleFacts.2 v a b ne]
        exact Finset.subset_inter (sub a) (eq ▸ sub b)
      have h := Finset.card_le_card incl
      have h2 := (small (f a)).1
      simp at h; omega
    let g (a : Fin 6) : ↥(Finset.univ.filter fun i => v ∈ B i) :=
      ⟨f a,Finset.mem_filter.mpr ⟨Finset.mem_univ _,member a⟩⟩
    have gi : Function.Injective g := fun a b h => fi (congrArg Subtype.val h)
    have hc := Fintype.card_le_of_injective g gi
    rw [Fintype.card_fin,Fintype.card_coe] at hc
    exact hc
  have bound : 6*missing.card ≤ 3*j := by
    calc
      6*missing.card = ∑ v ∈ missing, 6 := by simp [Nat.mul_comm]
      _ ≤ ∑ v ∈ missing, (Finset.univ.filter fun i => v ∈ B i).card := Finset.sum_le_sum six
      _ ≤ ∑ v : V, (Finset.univ.filter fun i => v ∈ B i).card := Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _
      _ = ∑ v : V, ∑ i : Fin j, if v ∈ B i then 1 else 0 := by simp
      _ = ∑ i : Fin j, ∑ v : V, if v ∈ B i then 1 else 0 := Finset.sum_comm
      _ = ∑ i : Fin j, (B i).card := by simp
      _ ≤ ∑ _i : Fin j, 3 := Finset.sum_le_sum fun i _ => (small i).2
      _ = 3*j := by simp [Nat.mul_comm]
  omega

private theorem uniqueWires {n m : ℕ} {B : Fin n → Finset V} (dist : Function.Injective B)
    (port : Fin n → Fin m) (obs : Fin m → V → Bool)
    (sig : ∀ i v, obs (port i) v = decide (v ∈ B i)) : Function.Injective port := by
  intro a b h
  apply dist
  ext v
  have hval : decide (v ∈ B a) = decide (v ∈ B b) := by rw [←sig, ←sig,h]
  exact decide_eq_decide.mp hval

private theorem cnfDeps {d : ℕ} (C : Circuit) (hC : FanInTwo C)
    (clauses : Finset (Finset (Fin d)))
    (irred : ∀ u ∈ clauses, ∀ v ∈ clauses, u ⊆ v → u = v)
    (T : Finset (Fin d)) (used : ∀ t ∈ T, ∃ u ∈ clauses, t ∈ u)
    (sem : ∀ x : Fin d → Bool, C.eval (List.ofFn x) = true ↔
      ∀ u ∈ clauses, ∃ v ∈ u, x v = true) : T.card ≤ C.size + 1 := by
  classical
  let F (x : Fin d → Bool) := C.eval (List.ofFn x)
  apply PEqualNP.MetaComplexity.Helpers.PermInputs.dep_lower_set d F T _ C.size ⟨C,hC,le_rfl,fun _ => rfl⟩
  intro t ht
  obtain ⟨u,hu,tu⟩ := used t ht
  let x (v : Fin d) := decide (v ∉ u)
  have old : C.eval (List.ofFn x) ≠ true := by
    intro yes
    obtain ⟨v,hv,vt⟩ := (sem x).mp yes u hu
    simp [x,hv] at vt
  have new : C.eval (List.ofFn (Function.update x t (!x t))) = true := by
    apply (sem _).mpr
    intro v hv
    by_cases same : v = u
    · exact ⟨t,same ▸ tu,by simp [x,tu]⟩
    · have ns : ¬v ⊆ u := fun sub => same (irred v hv u hu sub)
      obtain ⟨b,hb,bout⟩ := Finset.not_subset.mp ns
      have bne : b ≠ t := by rintro rfl; exact bout tu
      exact ⟨b,hb,by rw [Function.update_of_ne bne]; simp [x,bout]⟩
  exact ⟨x,fun eq => old (eq.symm.trans new)⟩

end PEqualNP.Research.PlaneBlockLowerBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.PlaneBlockLowerBound in
/-- The three stages below are actual gates on one common list of wires. The last circuit
    reads the preceding wires as inputs and combines block signals by an irredundant CNF.
    The line blocks cover the three-line side of each triangular negative input. -/
theorem PEqualNP.Research.PlaneBlockLowerBound
    (s j : ℕ) (single : Fin s → Fin 13) (blocks : Fin (s+j) → Finset (Fin 13))
    (pg lg mg : List Gate) (top : Circuit) (pointOut : Fin s → ℕ)
    (lineOut : Fin j → Fin lg.length) (midOut : Fin (s+j) → Fin mg.length)
    (clauses : Finset (Finset (Fin (26 + pg.length + lg.length + mg.length)))) :
    let I (p w : Fin 13) := p = w ∨ p = w+1 ∨ p = w+3 ∨ p = w+9
    let N (w : Fin 13) := ({w,w+1,w+3,w+9} : Finset (Fin 13)).image (Fin.castAdd 13)
    let B (i : Fin j) := blocks (Fin.natAdd s i)
    let input (w : Fin 13) := List.ofFn (fun k : Fin 26 => decide (k.val < 13 ∨ k = Fin.natAdd 13 w))
    let port (k : Fin (s+j)) : Fin (26 + pg.length + lg.length + mg.length) :=
      ⟨26 + pg.length + lg.length + (midOut k).val, by have h := (midOut k).isLt; omega⟩
    Function.Injective blocks → (∀ i, blocks (Fin.castAdd j i) = {single i}) →
    (∀ i, 2 ≤ (B i).card ∧ (B i).card ≤ 3) →
    (∀ v T, (∀ z, single z ≠ v) → v ∈ T → T.card = 3 → (¬∃ p, ∀ w ∈ T, I p w) →
      ∃ i, v ∈ B i ∧ B i ⊆ T) →
    (∀ g ∈ pg, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) →
    (∀ i (x : Fin 26 → Bool), (Circuit.mk pg (pointOut i)).eval (List.ofFn x) =
      decide (∃ v ∈ N (single i), x v = true)) →
    (∀ i w, ((Circuit.mk (pg ++ lg) 0).wires (input w)).getD (26 + pg.length + (lineOut i).val) false = decide (w ∈ B i)) →
    (∀ k w, ((Circuit.mk (pg ++ lg ++ mg) 0).wires (input w)).getD (port k).val false = decide (w ∈ blocks k)) →
    FanInTwo top → (∀ u ∈ clauses, ∀ v ∈ clauses, u ⊆ v → u = v) →
    (∀ k, ∃ u ∈ clauses, port k ∈ u) →
    (∀ x, top.eval (List.ofFn x) = true ↔ ∀ u ∈ clauses, ∃ v ∈ u, x v = true) →
    64+(13-s) ≤ (Circuit.mk (pg ++ lg ++ mg ++ top.gates) top.output).size := by
  dsimp only
  intro dist singles small cover ok pgEval lineEval midEval topOK irred used topEval
  have si : Function.Injective single := by
    intro a b h
    apply Fin.castAdd_injective s j
    apply dist
    rw [singles,singles,h]
  have sj := Fintype.card_le_of_injective single si
  simp only [Fintype.card_fin] at sj
  have charge := countBlocks single si (fun i => blocks (Fin.natAdd s i)) small cover
  have four : ∀ w : V, (points w).card = 4 := by decide +kernel
  have intersect : ∀ w r : V, w ≠ r → (points w ∩ points r).card ≤ 1 := by decide +kernel
  have word := PEqualNP.Outside.L_meta_529 26 s (fun i => points (single i))
    (fun a b ne => intersect _ _ (fun eq => ne (si eq))) pg pointOut ok pgEval
  simp only [four] at word
  have pointBound : 3*s ≤ pg.length := by simpa [Nat.mul_comm] using word
  let input (w : Fin 13) := List.ofFn (fun k : Fin 26 => decide (k.val < 13 ∨ k = Fin.natAdd 13 w))
  have ld : Function.Injective (fun i : Fin j => blocks (Fin.natAdd s i)) :=
    fun a b h => Fin.natAdd_injective j s (dist h)
  have li := uniqueWires ld lineOut (fun i w => ((Circuit.mk (pg ++ lg) 0).wires (input w)).getD (26+pg.length+i.val) false) lineEval
  have mi := uniqueWires dist midOut (fun i w => ((Circuit.mk (pg ++ lg ++ mg) 0).wires (input w)).getD (26+pg.length+lg.length+i.val) false) midEval
  have lineBound := Fintype.card_le_of_injective lineOut li
  have midBound := Fintype.card_le_of_injective midOut mi
  simp only [Fintype.card_fin] at lineBound midBound
  let port (k : Fin (s+j)) : Fin (26+pg.length+lg.length+mg.length) := ⟨26+pg.length+lg.length+(midOut k).val,by have := (midOut k).isLt; omega⟩
  have ip : Function.Injective port := by
    intro a b eq
    apply mi
    apply Fin.ext
    have eq' := congrArg Fin.val eq
    change 26+pg.length+lg.length+(midOut a).val = 26+pg.length+lg.length+(midOut b).val at eq'
    omega
  have upper := cnfDeps top topOK clauses irred (Finset.univ.image port) (by
    intro p hp
    obtain ⟨k,_,rfl⟩ := Finset.mem_image.mp hp
    exact used k) topEval
  rw [Finset.card_image_of_injective _ ip] at upper
  simp only [Finset.card_univ,Fintype.card_fin] at upper
  change _ ≤ (pg ++ lg ++ mg ++ top.gates).length
  change _ ≤ top.gates.length + 1 at upper
  simp only [List.length_append]
  omega
