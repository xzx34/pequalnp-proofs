import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.Research.CutCertificateWidth

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LowMergeProof

private def assignment {n m : ℕ} (P : Finset (Fin n)) (L : Finset (Fin m)) : Fin (n+m) → Bool :=
  Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))

private theorem assignment_mono {n m : ℕ} {P P' : Finset (Fin n)} {L L' : Finset (Fin m)}
    (hp : P ⊆ P') (hl : L ⊆ L') (k : Fin (n+m)) :
    assignment P L k = true → assignment P' L' k = true := by
  refine Fin.addCases (motive := fun i => assignment P L i = true → assignment P' L' i = true)
    (fun p => ?_) (fun l => ?_) k
  · simpa [assignment] using @hp p
  · simpa [assignment, Fin.addCases_right] using @hl l

private theorem ofFn_le {n : ℕ} {x y : Fin n → Bool} (h : ∀ i, x i = true → y i = true) :
    LeL (List.ofFn x) (List.ofFn y) := by
  intro i
  by_cases hi : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi)]
    simpa only [List.getElem_ofFn] using h ⟨i,hi⟩
  · intro hiBit
    rw [List.getD_eq_default _ _ (by simpa only [List.length_ofFn] using (Nat.le_of_not_gt hi))] at hiBit
    contradiction

private theorem append_on {u v : List Bool} (hl : u.length = v.length) (h : LeL u v) :
    LeL (u ++ [true]) (v ++ [true]) := by
  intro i hbit
  by_cases hi : i < u.length
  · rw [List.getD_append _ _ _ _ hi] at hbit
    rw [List.getD_append _ _ _ _ (by omega)]; exact h i hbit
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hbit ⊢
    simpa only [hl] using hbit

private theorem width {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (hc : ∀ p q l t, p ≠ q → l ≠ t → ¬ (I p l ∧ I p t ∧ I q l ∧ I q t))
    (A : Finset (Fin n)) (B D : Finset (Fin m))
    (hb : ∀ p ∈ A, ∃ l ∈ B, I p l) (hd : ∀ p ∈ A, ∃ l ∈ D, I p l) :
    (A.filter (fun p => ∀ l ∈ B ∩ D, ¬ I p l)).card ≤ (B \ D).card * (D \ B).card := by
  classical
  let S := A.filter (fun p => ∀ l ∈ B ∩ D, ¬ I p l)
  have cert (p : S) : ∃ b : ↥(B \ D), ∃ d : ↥(D \ B), I p.val b.val ∧ I p.val d.val := by
    rcases Finset.mem_filter.mp p.property with ⟨mem,away⟩
    obtain ⟨b, bB, ipc⟩ := hb p.val mem
    obtain ⟨d, dD, ipd⟩ := hd p.val mem
    exact ⟨⟨b, Finset.mem_sdiff.mpr ⟨bB, fun bD => away b (Finset.mem_inter.mpr ⟨bB,bD⟩) ipc⟩⟩,
           ⟨d, Finset.mem_sdiff.mpr ⟨dD, fun dB => away d (Finset.mem_inter.mpr ⟨dB,dD⟩) ipd⟩⟩,
           ipc, ipd⟩
  choose b d ib id using cert
  let f (p : S) : ↥(B \ D) × ↥(D \ B) := (b p, d p)
  have inj : Function.Injective f := by
    intro p q same
    apply Subtype.ext
    by_contra different
    have eqB : (b p).val = (b q).val := congrArg Subtype.val (congrArg Prod.fst same)
    have eqD : (d p).val = (d q).val := congrArg Subtype.val (congrArg Prod.snd same)
    have ne : (b p).val ≠ (d p).val := fun e =>
      (Finset.mem_sdiff.mp (b p).property).2 (e ▸ (Finset.mem_sdiff.mp (d p).property).1)
    exact hc p.val q.val (b p).val (d p).val different ne
      ⟨ib p, id p, eqB ▸ ib q, eqD ▸ id q⟩
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective f inj

end PEqualNP.Research.CutCertificateWidth

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LowMergeProof
open PEqualNP.Research.CutCertificateWidth

/-- At a shared wire, pure-line certificates for the forced-high suffix hit every point
    which activates the wire on its own. Outside the common lines of two certificates,
    distinct such points require distinct ordered pairs of lines. -/
theorem PEqualNP.Research.CutCertificateWidth (n m : ℕ) (I : Fin n → Fin m → Prop) [DecidableRel I]
    (hc : ∀ p q l t, p ≠ q → l ≠ t → ¬ (I p l ∧ I p t ∧ I q l ∧ I q t))
    (pre post : List Gate) (g : Gate) (out : ℕ) :
    let C : Circuit := ⟨pre ++ [g] ++ post, out⟩
    let x (P : Finset (Fin n)) (L : Finset (Fin m)) : Fin (n+m) → Bool :=
      Fin.addCases (motive := fun _ => Bool) (fun p => decide (p ∈ P)) (fun l => decide (l ∈ L))
    let W (P : Finset (Fin n)) (L : Finset (Fin m)) := (Circuit.mk pre 0).wires (List.ofFn (x P L))
    let U (P : Finset (Fin n)) (L : Finset (Fin m)) := g.op.eval (g.inputs.map fun i => (W P L).getD i false)
    let H (P : Finset (Fin n)) (L : Finset (Fin m)) := (Circuit.mk post out).eval (W P L ++ [true])
    Monotone2 C →
    (∀ z : Fin (n+m) → Bool, C.eval (List.ofFn z) = true →
      ∃ p l, I p l ∧ z (Fin.castAdd m p) = true ∧ z (Fin.natAdd n l) = true) →
    ∀ A : Finset (Fin n), (∀ p ∈ A, U {p} ∅ = true) →
      (∀ B : Finset (Fin m), H ∅ B = true → ∀ p ∈ A, ∃ l ∈ B, I p l) ∧
      (∀ B D : Finset (Fin m), H ∅ B = true → H ∅ D = true →
        (A.filter (fun p => ∀ l ∈ B ∩ D, ¬ I p l)).card ≤ (B \ D).card * (D \ B).card) ∧
      (∀ t : Fin m, H ∅ {t} = true →
        (∀ p ∈ A, I p t) ∧ ∀ B : Finset (Fin m), t ∉ B → H ∅ B = true → A.card ≤ B.card) := by
  dsimp only
  intro mono safe A signal
  let W (P : Finset (Fin n)) (L : Finset (Fin m)) :=
    pre.foldl step (List.ofFn (assignment P L))
  let U (P : Finset (Fin n)) (L : Finset (Fin m)) := g.op.eval (g.inputs.map fun i => (W P L).getD i false)
  let H (P : Finset (Fin n)) (L : Finset (Fin m)) := (Circuit.mk post out).eval (W P L ++ [true])
  change ∀ p ∈ A, U {p} ∅ = true at signal
  have prele {P Q : Finset (Fin n)} {B D : Finset (Fin m)} (hp : P ⊆ Q) (hb : B ⊆ D) :
      LeL (W P B) (W Q D) :=
    fold_mono pre (fun k hk => (mono k (by simp [hk])).1) _ _ (by simp) (ofFn_le (assignment_mono hp hb))
  have len (P : Finset (Fin n)) (L : Finset (Fin m)) : (W P L).length = n+m+pre.length := by
    simp [W,fold_length]
  have hit (B : Finset (Fin m)) (ok : H ∅ B = true) (p : Fin n) (mem : p ∈ A) : ∃ l ∈ B, I p l := by
    have hU : U {p} B = true :=
      eval_mono g.op (mono g (by simp)).1 g.inputs _ _
        (prele (Finset.Subset.refl _) (Finset.empty_subset B)) (signal p mem)
    have hH : H {p} B = true :=
      fold_mono post (fun k hk => (mono k (by simp [hk])).1) _ _ (by simp [len])
        (append_on (by simp [len]) (prele (Finset.empty_subset {p}) (Finset.Subset.refl B))) out ok
    have actual : (Circuit.mk (pre ++ [g] ++ post) out).eval (List.ofFn (assignment {p} B)) = true := by
      change ((pre ++ [g] ++ post).foldl step (List.ofFn (assignment {p} B))).getD out false = true
      simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
      change (post.foldl step (W {p} B ++ [U {p} B])).getD out false = true
      rw [hU]; exact hH
    obtain ⟨q,l,e,hq,hl⟩ := safe _ actual
    have qp : q = p := by simpa [assignment] using hq
    have lB : l ∈ B := by simpa [assignment,Fin.addCases_right] using hl
    exact ⟨l,lB, qp ▸ e⟩
  refine ⟨hit, fun B D hB hD => width I hc A B D (hit B hB) (hit D hD), ?_⟩
  intro t ht
  have allOn (p : Fin n) (hp : p ∈ A) : I p t := by
    obtain ⟨l,hl,he⟩ := hit {t} ht p hp
    simpa [Finset.mem_singleton.mp hl] using he
  refine ⟨allOn, ?_⟩
  intro B htB hB
  have bound := width I hc A {t} B (hit {t} ht) (hit B hB)
  have dis : Disjoint ({t} : Finset (Fin m)) B := Finset.disjoint_singleton_left.mpr htB
  simpa [Finset.disjoint_iff_inter_eq_empty.mp dis, dis.sdiff_eq_left, dis.symm.sdiff_eq_left] using bound
