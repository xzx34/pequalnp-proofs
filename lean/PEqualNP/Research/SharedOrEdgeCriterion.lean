import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowMergeWires

namespace PEqualNP.Research.SharedOrEdgeCriterion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.LowMergeProof

private theorem append_le (w v : List Bool) (p q : Bool) (len : w.length = v.length)
    (before : LeL w v) (bit : p = true → q = true) : LeL (w ++ [p]) (v ++ [q]) := by
  intro i hi
  by_cases early : i < w.length
  · rw [List.getD_append _ _ _ _ early] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact before i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    rw [← len]
    cases h : i - w.length with
    | zero => rw [h] at hi; exact bit hi
    | succ t => simp [h] at hi

private theorem pairValues (w : List Bool) (k a b c : ℕ) (len : w.length = k)
    (ha : a < k) (hb : b < k) (dom : w.getD a false = true → w.getD b false = true) :
    let p := w.getD a false || w.getD c false
    let q := w.getD c false && w.getD b false
    let t := p && w.getD b false
    ([⟨.or, [a,c]⟩, ⟨.and, [k,b]⟩] : List Gate).foldl step w = w ++ [p,t] ∧
    ([⟨.and, [c,b]⟩, ⟨.or, [a,k]⟩] : List Gate).foldl step w = w ++ [q,t] := by
  subst k
  have absorb : (w.getD a false || (w.getD c false && w.getD b false)) =
      ((w.getD a false || w.getD c false) && w.getD b false) := by
    cases ea : w.getD a false <;> cases eb : w.getD b false <;> simp_all
  dsimp only
  have readA (v : Bool) : (w ++ [v]).getD a false = w.getD a false :=
    List.getD_append _ _ _ _ ha
  have readB (v : Bool) : (w ++ [v]).getD b false = w.getD b false :=
    List.getD_append _ _ _ _ hb
  have readLast (v : Bool) : (w ++ [v]).getD w.length false = v := by simp
  simp only [List.foldl_cons, List.foldl_nil, step, GateOp.eval, List.map_cons, List.map_nil,
    List.any_cons, List.all_cons, List.any_nil, List.all_nil, id_eq, Bool.or_false,
    Bool.and_true, readA, readB, readLast, absorb, List.append_assoc, List.cons_append,
    List.nil_append, and_self]

private theorem bitLe (u v : Bool) (h : u = true → v = true) : u.toNat ≤ v.toNat := by
  cases u <;> cases v <;> simp_all

private theorem bitsStrict (u v : Bool) (h : u = true → v = true) (diff : v ≠ u) :
    u.toNat < v.toNat := by
  cases u <;> cases v <;> simp_all

private theorem pairInput_le {n : ℕ} (x : Fin n → Bool) (i j : Fin n)
    (hi : x i = true) (hj : x j = true) :
    LeL (List.ofFn (fun k : Fin n => decide (k = i ∨ k = j))) (List.ofFn x) := by
  intro k hv
  by_cases hk : k < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hk), List.getElem_ofFn] at hv ⊢
    rcases of_decide_eq_true hv with e | e
    · simpa [e] using hi
    · simpa [e] using hj
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hv
    contradiction

end PEqualNP.Research.SharedOrEdgeCriterion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.LowMergeProof
open PEqualNP.Research.SharedOrEdgeCriterion

/-- The shared OR may have arbitrarily many later readers. Every wire can only move
    downward, and a change of the graph function is witnessed on the endpoints of
    an edge where the intermediate wire changes. -/
theorem PEqualNP.Research.SharedOrEdgeCriterion (n : ℕ) (E : Fin n → Fin n → Prop)
    (pre post : List Gate) (a b c out : ℕ) (ha : a < n + pre.length) (hb : b < n + pre.length) :
    let k := n + pre.length
    let old : Circuit := ⟨pre ++ [⟨.or, [a,c]⟩, ⟨.and, [k,b]⟩] ++ post, out⟩
    let new : Circuit := ⟨pre ++ [⟨.and, [c,b]⟩, ⟨.or, [a,k]⟩] ++ post, out⟩
    let W := fun (x : Fin n → Bool) => (Circuit.mk pre 0).wires (List.ofFn x)
    let edge := fun (i j t : Fin n) => decide (t = i ∨ t = j)
    let single := fun (v t : Fin n) => decide (v = t)
    let activity := fun (D : Circuit) => ∑ v : Fin n, ∑ j ∈ Finset.range (n + D.size),
      ((D.wires (List.ofFn (single v))).getD j false).toNat
    Monotone2 old →
    (∀ x : Fin n → Bool, (W x).getD a false = true → (W x).getD b false = true) →
    (∀ x : Fin n → Bool, old.eval (List.ofFn x) = true ↔
      ∃ i j, E i j ∧ x i = true ∧ x j = true) →
    new.size = old.size ∧ Monotone2 new ∧
    (∀ (x : Fin n → Bool) (i : ℕ), (new.wires (List.ofFn x)).getD i false = true →
      (old.wires (List.ofFn x)).getD i false = true) ∧
    ((∃ v, let w := W (single v); (w.getD a false || w.getD c false) ≠
       (w.getD c false && w.getD b false)) → activity new < activity old) ∧
    ((∀ x : Fin n → Bool, new.eval (List.ofFn x) = old.eval (List.ofFn x)) ↔
     ∀ i j, E i j →
       (let w := W (edge i j); (w.getD a false || w.getD c false) ≠
         (w.getD c false && w.getD b false)) → new.eval (List.ofFn (edge i j)) = true) := by
  dsimp only
  intro mono dom oldSpec
  let k := n + pre.length
  let S : List Gate := [⟨.or, [a,c]⟩, ⟨.and, [k,b]⟩]
  let T : List Gate := [⟨.and, [c,b]⟩, ⟨.or, [a,k]⟩]
  let C : Circuit := ⟨pre ++ S ++ post, out⟩
  let D : Circuit := ⟨pre ++ T ++ post, out⟩
  let W (x : Fin n → Bool) := pre.foldl step (List.ofFn x)
  let p (x : Fin n → Bool) := (W x).getD a false || (W x).getD c false
  let q (x : Fin n → Bool) := (W x).getD c false && (W x).getD b false
  let t (x : Fin n → Bool) := p x && (W x).getD b false
  let edge (i j z : Fin n) := decide (z = i ∨ z = j)
  change Monotone2 C at mono
  change ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ _ at oldSpec
  have monD : Monotone2 D := by
    intro g hg
    change g ∈ pre ++ T ++ post at hg
    simp only [T, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (h | rfl | rfl) | h
    · exact mono g (by simp [C,h])
    · simp
    · simp
    · exact mono g (by simp [C,h])
  have forms (x : Fin n → Bool) :
      C.wires (List.ofFn x) = post.foldl step (W x ++ [p x,t x]) ∧
      D.wires (List.ofFn x) = post.foldl step (W x ++ [q x,t x]) := by
    have len : (W x).length = k := by simp [W, k, fold_length]
    obtain ⟨hs, ht⟩ := pairValues (W x) k a b c len ha hb (dom x)
    change ((pre ++ S ++ post).foldl step (List.ofFn x) = _) ∧
      ((pre ++ T ++ post).foldl step (List.ofFn x) = _)
    simp only [List.foldl_append]
    exact ⟨congrArg (post.foldl step) hs, congrArg (post.foldl step) ht⟩
  have down (x : Fin n → Bool) : LeL (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    rw [(forms x).1, (forms x).2]
    apply fold_mono post (fun g hg => (mono g (by simp [C,hg])).1) _ _ (by simp)
    have first : LeL (W x ++ [q x]) (W x ++ [p x]) := by
      apply append_le _ _ _ _ rfl (fun _ h => h)
      simp [p,q]
      tauto
    simpa [List.append_assoc] using (append_le _ _ (t x) (t x) (by simp) first id)
  let single (v t : Fin n) := decide (v = t)
  have sameSize : D.size = C.size := by simp [C,D,S,T,Circuit.size]
  refine ⟨sameSize, monD, down, ?_, ?_⟩
  · change (∃ v, p (single v) ≠ q (single v)) →
      (∑ v : Fin n, ∑ j ∈ Finset.range (n + D.size), ((D.wires (List.ofFn (single v))).getD j false).toNat) <
      ∑ v : Fin n, ∑ j ∈ Finset.range (n + C.size), ((C.wires (List.ofFn (single v))).getD j false).toNat
    rintro ⟨v, diff⟩
    rw [sameSize]
    have weak (u : Fin n) (j : ℕ) := bitLe _ _ (down (single u) j)
    apply Finset.sum_lt_sum (fun u _ => Finset.sum_le_sum (fun j _ => weak u j))
    refine ⟨v, Finset.mem_univ _, Finset.sum_lt_sum (fun j _ => weak v j) ?_⟩
    have inside : k ∈ Finset.range (n + C.size) := by simp [C, k, S, Circuit.size]
    refine ⟨k, inside, bitsStrict _ _ (down (single v) k) ?_⟩
    have len : (W (single v)).length = k := by simp [W, k, fold_length]
    have atK (b₁ b₂ : Bool) : (post.foldl step (W (single v) ++ [b₁,b₂])).getD k false = b₁ := by
      rw [fold_getD_lt _ _ _ (by simp [len]), List.getD_append_right _ _ _ _ (by omega), len, Nat.sub_self]
      rfl
    rwa [(forms _).1, (forms _).2, atK, atK]
  · change (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ↔
      ∀ i j, E i j → p (edge i j) ≠ q (edge i j) → D.eval (List.ofFn (edge i j)) = true
    constructor
    · intro same i j e _
      rw [same]
      exact (oldSpec _).2 ⟨i,j,e,by simp [edge],by simp [edge]⟩
    · intro good x
      cases hx : C.eval (List.ofFn x) with
      | false =>
        cases hd : D.eval (List.ofFn x) with
        | false => rfl
        | true => exact Bool.noConfusion ((down x out hd).symm.trans hx)
      | true =>
        obtain ⟨i,j,e,hi,hj⟩ := (oldSpec x).1 hx
        have hit : D.eval (List.ofFn (edge i j)) = true := by
          by_cases eq : p (edge i j) = q (edge i j)
          · have wires : D.wires (List.ofFn (edge i j)) = C.wires (List.ofFn (edge i j)) := by
              rw [(forms _).1, (forms _).2, eq]
            change (D.wires _).getD out false = true
            rw [wires]
            exact (oldSpec _).2 ⟨i,j,e,by simp [edge],by simp [edge]⟩
          · exact good i j e eq
        exact wires_mono D (fun g hg => (monD g hg).1) _ _ (by simp) (pairInput_le x i j hi hj) out hit
