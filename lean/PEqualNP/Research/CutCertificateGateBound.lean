import PEqualNP.Outside.L_meta_529
import PEqualNP.Research.CutCertificateWidth

namespace PEqualNP.Research.CutCertificateGateBound

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

private def rows {n m : ℕ} (P : Finset (Fin n)) (B : Finset (Fin m)) : Fin (n+m) → Bool :=
  Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ P)) (fun l => decide (l ∈ B))

private theorem update_row {n m : ℕ} (B : Finset (Fin m)) (l : Fin m) :
    Function.update (rows (∅ : Finset (Fin n)) B) (Fin.natAdd n l) false = rows ∅ (B.erase l) := by
  funext i
  refine Fin.addCases (motive := fun j => Function.update (rows (∅ : Finset (Fin n)) B) (Fin.natAdd n l) false j = rows ∅ (B.erase l) j)
    (fun p => ?_) (fun q => ?_) i
  · have ne : Fin.castAdd m p ≠ Fin.natAdd n l := by
      intro h
      have eq := congrArg Fin.val h
      simp only [Fin.val_castAdd,Fin.val_natAdd] at eq
      omega
    rw [Function.update_of_ne ne]; simp [rows]
  · by_cases h : q = l
    · subst q; simp [rows,Fin.addCases_right]
    · have ne : Fin.natAdd n q ≠ Fin.natAdd n l := by
        intro eq; apply h; exact Fin.natAdd_injective m n eq
      rw [Function.update_of_ne ne]; simp [rows,Fin.addCases_right,h]

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

end PEqualNP.Research.CutCertificateGateBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.CutCertificateGateBound

/-- Two disjoint pure-line certificates force binary AND gates away from the cut.
    A singleton certificate and a disjoint certificate give the stronger linear bound. -/
theorem PEqualNP.Research.CutCertificateGateBound (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I]
    (hc : ∀ p q l t, p ≠ q → l ≠ t → ¬ (I p l ∧ I p t ∧ I q l ∧ I q t))
    (pre post : List Gate) (g : Gate) (out : ℕ) :
    let C : Circuit := ⟨pre ++ [g] ++ post, out⟩
    let row (P : Finset (Fin n)) (L : Finset (Fin m)) : Fin (n+m) → Bool :=
      Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
    let W (P : Finset (Fin n)) (L : Finset (Fin m)) := (Circuit.mk pre 0).wires (List.ofFn (row P L))
    let U (p : Fin n) := g.op.eval (g.inputs.map fun i => (W {p} ∅).getD i false)
    let H (L : Finset (Fin m)) := (Circuit.mk post out).eval (W ∅ L ++ [true])
    let k := (pre ++ post).countP (fun h => h.op.casesOn (motive := fun _ => Bool) (decide (h.inputs.length = 2)) false false (fun _ => false) false)
    Monotone2 C →
    (∀ z : Fin (n+m) → Bool, C.eval (List.ofFn z) = true →
      ∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) →
    ∀ A : Finset (Fin n), (∀ p ∈ A, U p = true) →
      (∀ B D : Finset (Fin m), Disjoint B D → H B = true → H D = true → A.card ≤ (k + 1)^2) ∧
      (∀ t : Fin m, ∀ B : Finset (Fin m), t ∉ B → H {t} = true → H B = true → A.card ≤ k + 1) := by
  dsimp only
  intro mono safe A on
  let H (L : Finset (Fin m)) := (Circuit.mk post out).eval ((Circuit.mk pre 0).wires (List.ofFn (rows (∅ : Finset (Fin n)) L)) ++ [true])
  let K := (pre ++ post).countP pay
  let forced : Circuit := ⟨pre ++ [⟨.and,[]⟩] ++ post,out⟩
  have legal : Monotone2 forced := by
    intro gate mem
    change gate ∈ pre ++ [_] ++ post at mem
    simp only [List.mem_append, List.mem_singleton] at mem
    rcases mem with (h | rfl) | h
    · exact mono gate (by simp [h])
    · simp
    · exact mono gate (by simp [h])
  have sim (L : Finset (Fin m)) : forced.eval (List.ofFn (rows (∅ : Finset (Fin n)) L)) = H L := by
    simp [forced,H,Circuit.eval,Circuit.wires,List.foldl_append,GateOp.eval]
  have affordable (D : Finset (Fin m)) (dOn : H D = true) :
      ∃ B ⊆ D, H B = true ∧ B.card ≤ K + 1 := by
    obtain ⟨B,bD,bOn,minimum⟩ := shrink H D dOn
    refine ⟨B,bD,bOn,?_⟩
    let x := rows (∅ : Finset (Fin n)) B
    let S := Finset.univ.filter fun j : Fin (n+m) => forced.eval (List.ofFn (Function.update x j false)) = false
    have sub : B.image (Fin.natAdd n) ⊆ S := by
      intro j hj
      obtain ⟨l,lB,rfl⟩ := Finset.mem_image.mp hj
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      change forced.eval (List.ofFn (Function.update (rows (∅ : Finset (Fin n)) B) (Fin.natAdd n l) false)) = false
      rw [update_row,sim]; exact minimum l lB
    have nS : S.card ≤ forced.gates.countP pay + 1 := falling _ forced x legal ((sim B).trans bOn)
    have cardB := Finset.card_le_card sub
    rw [Finset.card_image_of_injective _ (Fin.natAdd_injective m n)] at cardB
    have count : forced.gates.countP pay = K := by simp [K,forced,pay,List.countP_append,Nat.add_assoc]
    exact cardB.trans (count ▸ nS)
  obtain ⟨_,width,single⟩ := PEqualNP.Research.CutCertificateWidth n m I hc pre post g out mono safe A on
  constructor
  · intro D₁ D₂ dis h₁ h₂
    change A.card ≤ (K + 1)^2
    obtain ⟨B,b₁,bOn,smallB⟩ := affordable D₁ h₁
    obtain ⟨D,d₂,dOn,smallD⟩ := affordable D₂ h₂
    have dis' : Disjoint B D := dis.mono b₁ d₂
    have h := width B D bOn dOn
    have result : A.card ≤ B.card * D.card := by
      simpa [Finset.disjoint_iff_inter_eq_empty.mp dis',dis'.sdiff_eq_left,dis'.symm.sdiff_eq_left] using h
    exact result.trans (by simpa only [pow_two] using Nat.mul_le_mul smallB smallD)
  · intro t D away h₁ h₂
    obtain ⟨B,bD,bOn,small⟩ := affordable D h₂
    exact ((single t h₁).2 B (fun e => away (bD e)) bOn).trans small
