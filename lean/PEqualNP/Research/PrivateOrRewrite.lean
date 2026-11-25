import PEqualNP.Defs

namespace PEqualNP.Research.PrivateOrRewrite

open PEqualNP.CircuitLowerBounds

private def step (xs : List Bool) (g : Gate) :=
  xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)]

private theorem peek (xs : List Bool) (a : Bool) (i : ℕ) :
    (xs ++ [a]).getD i false = if i = xs.length then a else xs.getD i false := by
  by_cases lt : i < xs.length
  · rw [List.getD_append _ _ _ _ lt, if_neg (Nat.ne_of_lt lt)]
  · by_cases eq : i = xs.length
    · subst i
      simp [List.getD_eq_getElem?_getD]
    · rw [if_neg eq, List.getD_eq_default (xs ++ [a]) false (by simp; omega),
          List.getD_eq_default xs false (by omega)]

private theorem preserve (k : ℕ) (gs : List Gate) (privateWire : ∀ g ∈ gs, k ∉ g.inputs)
    (xs ys : List Bool) (lengths : xs.length = ys.length)
    (agree : ∀ i, i ≠ k → xs.getD i false = ys.getD i false) :
    ∀ i, i ≠ k → (gs.foldl step xs).getD i false = (gs.foldl step ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact agree
  | cons g gs ih =>
    have same : g.inputs.map (fun i => xs.getD i false) = g.inputs.map (fun i => ys.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact agree i fun e => privateWire g List.mem_cons_self (e ▸ hi)
    apply ih (fun g' hg' => privateWire g' (List.mem_cons_of_mem _ hg'))
    · simp [step, lengths]
    · intro i hi
      simp only [step, peek, lengths, same, agree i hi]

private theorem prefix_length (gs : List Gate) (xs : List Bool) :
    (gs.foldl step xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp
  | cons g gs ih => simp [ih, step, Nat.add_comm, Nat.add_left_comm]

end PEqualNP.Research.PrivateOrRewrite

open PEqualNP.CircuitLowerBounds PEqualNP.Research.PrivateOrRewrite in
/-- Pull a dominated wire out of a private OR followed by AND, at equal cost.
The replacement AND accepts a subset of the old AND's inputs. A witness
turning on `a` and turning off `c` disappears from that AND. -/
theorem PEqualNP.Research.PrivateOrRewrite (n : ℕ) (pre post : List Gate) (a b c out : ℕ)
    (ha : a < n + pre.length) (hb : b < n + pre.length) (hc : c < n + pre.length)
    (hout : out ≠ n + pre.length) (hp : ∀ g ∈ post, n + pre.length ∉ g.inputs)
    (dom : ∀ x : Fin n → Bool, let w := (Circuit.mk pre 0).wires (List.ofFn x)
      w.getD a false = true → w.getD b false = true) :
    let k := n + pre.length
    let old : Circuit := ⟨pre ++ [⟨.or, [a,c]⟩, ⟨.and, [k,b]⟩] ++ post, out⟩
    let new : Circuit := ⟨pre ++ [⟨.and, [c,b]⟩, ⟨.or, [a,k]⟩] ++ post, out⟩
    new.size = old.size ∧
    (PEqualNP.MetaComplexity.Monotone2 old → PEqualNP.MetaComplexity.Monotone2 new) ∧
    (PEqualNP.MetaComplexity.NestedCover.ReadsBack n old → PEqualNP.MetaComplexity.NestedCover.ReadsBack n new) ∧
    (∀ x : Fin n → Bool, new.eval (List.ofFn x) = old.eval (List.ofFn x)) ∧
    ∀ x : Fin n → Bool, let w := (Circuit.mk pre 0).wires (List.ofFn x)
      ((w.getD c false && w.getD b false) = true → ((w.getD a false || w.getD c false) && w.getD b false) = true) ∧
      (w.getD a false = true → w.getD c false = false →
       (w.getD c false && w.getD b false) = false ∧ ((w.getD a false || w.getD c false) && w.getD b false) = true) := by
  dsimp only
  refine ⟨by simp [Circuit.size], ?_, ?_, ?_, ?_⟩
  · intro mono g hg
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (h | rfl | rfl) | h
    · exact mono g (by simp [h])
    · simp
    · simp
    · exact mono g (by simp [h])
  · intro back j hj i hi
    let pair₁ : List Gate := [⟨.or, [a,c]⟩, ⟨.and, [n + pre.length,b]⟩]
    let pair₂ : List Gate := [⟨.and, [c,b]⟩, ⟨.or, [a,n + pre.length]⟩]
    let dummy : Gate := ⟨.or, []⟩
    have sameLen : (pre ++ pair₁).length = (pre ++ pair₂).length := by simp [pair₁, pair₂]
    have sameBound : j < ((pre ++ pair₁) ++ post).length := by
      change j < ((pre ++ pair₂) ++ post).length at hj
      simpa only [List.length_append, pair₁, pair₂, List.length_cons, List.length_nil] using hj
    have applyOld (h : i ∈ ((pre ++ pair₁ ++ post).getD j dummy).inputs) : i < n + j :=
      back j sameBound i h
    change i ∈ ((pre ++ pair₂ ++ post).getD j dummy).inputs at hi
    by_cases early : j < pre.length
    · have l₁ : j < (pre ++ pair₁).length := by simp [pair₁]; omega
      have l₂ : j < (pre ++ pair₂).length := by simp [pair₂]; omega
      rw [List.getD_append _ _ _ _ l₂, List.getD_append _ _ _ _ early] at hi
      apply applyOld
      rwa [List.getD_append _ _ _ _ l₁, List.getD_append _ _ _ _ early]
    · by_cases late : (pre ++ pair₂).length ≤ j
      · rw [List.getD_append_right _ _ _ _ late] at hi
        apply applyOld
        rwa [List.getD_append_right _ _ _ _ (sameLen.trans_le late), sameLen]
      · have bet : j = pre.length ∨ j = pre.length + 1 := by simp [pair₂] at late; omega
        have hlt : j < (pre ++ pair₂).length := by omega
        rw [List.getD_append _ _ _ _ hlt, List.getD_append_right _ _ _ _ (by omega : pre.length ≤ j)] at hi
        rcases bet with rfl | rfl <;> simp [pair₂] at hi <;> (rcases hi with rfl | rfl) <;> omega
  · intro x
    let w := pre.foldl step (List.ofFn x)
    have len : w.length = n + pre.length := by simp [w, prefix_length]
    have da := dom x
    change w.getD a false = true → w.getD b false = true at da
    have absorb : (w.getD a false || (w.getD c false && w.getD b false)) =
        ((w.getD a false || w.getD c false) && w.getD b false) := by
      cases ea : w.getD a false <;> cases eb : w.getD b false <;> simp_all
    change ((pre ++ [_, _] ++ post).foldl step (List.ofFn x)).getD out false =
      ((pre ++ [_, _] ++ post).foldl step (List.ofFn x)).getD out false
    simp only [List.foldl_append]
    change (post.foldl step ([⟨.and, [c,b]⟩, ⟨.or, [a,n + pre.length]⟩].foldl step w)).getD out false =
      (post.foldl step ([⟨.or, [a,c]⟩, ⟨.and, [n + pre.length,b]⟩].foldl step w)).getD out false
    apply preserve (n + pre.length) post hp _ _ _ _ out hout
    · simp [step]
    · intro i hi
      have na : a ≠ n + pre.length := Nat.ne_of_lt ha
      have nb : b ≠ n + pre.length := Nat.ne_of_lt hb
      simp only [List.foldl_cons, List.foldl_nil, step, List.map_cons, List.map_nil,
        GateOp.eval, List.all_cons, List.any_cons, List.all_nil, List.any_nil,
        id_eq, Bool.and_true, Bool.or_false, peek, List.length_append, List.length_cons,
        List.length_nil, len, na, nb, hi, ite_true, ite_false, absorb]
  · intro x
    have da := dom x
    dsimp only at da ⊢
    generalize (Circuit.mk pre 0).wires (List.ofFn x) = w at da ⊢
    cases ea : w.getD a false <;> cases eb : w.getD b false <;> cases ec : w.getD c false <;> simp_all
