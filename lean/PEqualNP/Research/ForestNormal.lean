import PEqualNP.Defs
import PEqualNP.MetaComplexity.L104
import PEqualNP.MetaComplexity.L204

namespace PEqualNP.Research.ForestNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

private abbrev vals (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

private abbrev allowed (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

private def run (P : Prop) (w : List Bool) : List Gate → Prop
  | [] => True
  | g :: gs => allowed g ∧ (∀ i ∈ g.inputs, i < w.length) ∧
    (P → g.op = .and → vals w g = false) ∧ run P (w ++ [vals w g]) gs

private theorem run_append (P : Prop) (A B : List Gate) (w : List Bool)
    (ha : run P w A) (hb : run P (wiresFrom A w) B) : run P w (A ++ B) := by
  induction A generalizing w with
  | nil => exact hb
  | cons g gs ih => exact ⟨ha.1, ha.2.1, ha.2.2.1, ih _ ha.2.2.2 hb⟩

private theorem run_info {P : Prop} {gs : List Gate} {w : List Bool} (h : run P w gs) :
    ∀ j < gs.length, let g := gs.getD j ⟨.or,[]⟩
      allowed g ∧ (∀ i ∈ g.inputs, i < w.length+j) ∧
        (P → g.op = .and → (wiresFrom gs w).getD (w.length+j) false = false) := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    intro j hj
    cases j with
    | zero =>
      simp only [List.getD_cons_zero, Nat.add_zero]
      refine ⟨h.1, h.2.1, ?_⟩
      intro hp hop
      change (wiresFrom gs (w ++ [vals w g])).getD w.length false = false
      rw [getD_wiresFrom _ _ _ (by simp)]
      simpa [List.getD_eq_getElem?_getD] using h.2.2.1 hp hop
    | succ j =>
      have hi := ih h.2.2.2 j (by simpa using hj)
      have push : wiresFrom (g :: gs) w = wiresFrom gs (w ++ [vals w g]) := rfl
      simp only [push]
      simpa only [List.getD_cons_succ, List.length_append, List.length_singleton, Nat.add_assoc,
        Nat.add_comm 1 j] using hi

private def Bld {n : ℕ} (P : (Fin n → Bool) → Prop) (F : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∀ m, n ≤ m → ∃ (gs : List Gate) (out : ℕ), gs.length ≤ s ∧ out < m + gs.length ∧
    ∀ w : List Bool, w.length = m → run (P (fun i => w.getD i false)) w gs ∧
      (wiresFrom gs w).getD out false = F (fun i => w.getD i false)

private theorem bld_mono {n : ℕ} {P : (Fin n → Bool) → Prop} {F : (Fin n → Bool) → Bool} {s s' : ℕ}
    (h : Bld P F s) (hs : s ≤ s') : Bld P F s' := by
  intro m hm
  obtain ⟨gs, o, l, ho, ev⟩ := h m hm
  exact ⟨gs, o, l.trans hs, ho, ev⟩

private theorem bld_congr {n : ℕ} {P : (Fin n → Bool) → Prop} {F H : (Fin n → Bool) → Bool} {s : ℕ}
    (h : Bld P F s) (eq : ∀ x, F x = H x) : Bld P H s := (funext eq) ▸ h

private theorem bld_var {n : ℕ} {P : (Fin n → Bool) → Prop} (i : Fin n) : Bld P (fun x => x i) 0 := by
  intro m hm
  exact ⟨[],i,le_rfl,by simpa using Nat.lt_of_lt_of_le i.isLt hm,fun _ _ => ⟨trivial,rfl⟩⟩

private theorem bld_bin {n : ℕ} {P : (Fin n → Bool) → Prop} (op : GateOp)
    (hop : op = .and ∨ op = .or) (c : Bool → Bool → Bool) (hc : ∀ a b, op.eval [a,b] = c a b)
    {F H : (Fin n → Bool) → Bool} {s₁ s₂ : ℕ} (b₁ : Bld P F s₁) (b₂ : Bld P H s₂)
    (hzero : ∀ x, P x → op = .and → c (F x) (H x) = false) :
    Bld P (fun x => c (F x) (H x)) (s₁+s₂+1) := by
  intro m hm
  obtain ⟨gs, a, ga, ha, ea⟩ := b₁ m hm
  obtain ⟨hs, b, gb, hb, eb⟩ := b₂ (m+gs.length) (by omega)
  let g : Gate := ⟨op,[a,b]⟩
  refine ⟨gs ++ hs ++ [g], m+gs.length+hs.length, by simp; omega, by simp; omega, ?_⟩
  intro w hw
  let v := wiresFrom gs w
  let u := wiresFrom hs v
  have lv : v.length = m+gs.length := by simp [v, length_wiresFrom, hw]
  have lu : u.length = m+gs.length+hs.length := by simp [u, length_wiresFrom, lv]
  have same : (fun i : Fin n => v.getD i false) = (fun i : Fin n => w.getD i false) := by
    funext i; exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
  have ⟨r₁, v₁⟩ := ea w hw
  have ⟨r₂, v₂⟩ := eb v lv
  rw [same] at r₂ v₂
  have ya : u.getD a false = F (fun i => w.getD i false) := by
    rw [show u.getD a false = v.getD a false from getD_wiresFrom _ _ _ (by omega)]
    exact v₁
  have value : vals u g = c (F (fun i => w.getD i false)) (H (fun i => w.getD i false)) := by
    change op.eval [u.getD a false, u.getD b false] = _
    rw [hc, ya, show u.getD b false = _ from v₂]
  constructor
  · apply run_append _ _ _ _ (run_append _ _ _ _ r₁ r₂)
    rw [wiresFrom_append]
    refine ⟨⟨hop, Nat.le_refl 2⟩, ?_, ?_, trivial⟩
    · intro i hi; change i ∈ [a,b] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      change i < u.length
      omega
    · exact fun hp h => value.trans (hzero _ hp h)
  · rw [wiresFrom_append, wiresFrom_append]
    change (u ++ [vals u g]).getD (m+gs.length+hs.length) false = _
    rw [← lu, getD_snoc_eq, value]

private theorem bld_or {n : ℕ} {P : (Fin n → Bool) → Prop} {F H : (Fin n → Bool) → Bool} {s₁ s₂ : ℕ}
    (h₁ : Bld P F s₁) (h₂ : Bld P H s₂) : Bld P (fun x => F x || H x) (s₁+s₂+1) :=
  bld_bin .or (Or.inr rfl) (· || ·) (by simp [GateOp.eval]) h₁ h₂ (by simp)

private theorem bld_and {n : ℕ} {P : (Fin n → Bool) → Prop} {F H : (Fin n → Bool) → Bool} {s₁ s₂ : ℕ}
    (h₁ : Bld P F s₁) (h₂ : Bld P H s₂) (hz : ∀ x, P x → (F x && H x) = false) :
    Bld P (fun x => F x && H x) (s₁+s₂+1) :=
  bld_bin .and (Or.inl rfl) (· && ·) (by simp [GateOp.eval]) h₁ h₂ (fun x hx _ => hz x hx)

-- The star partition below follows EdgeUpperMono.bld_edges, with the independent-input gate invariant.
private theorem bld_anyList {n : ℕ} {P : (Fin n → Bool) → Prop} (vs : List (Fin n)) : ∀ v : Fin n,
    Bld P (fun x => (v :: vs).any fun j => x j) vs.length := by
  induction vs with
  | nil => intro v; exact bld_congr (bld_var v) (by intro x; simp)
  | cons w ws ih =>
    intro v
    have := bld_or (bld_var v) (ih w)
    refine bld_congr (bld_mono this (by simp)) ?_
    intro x
    simp

/-- The OR of the inputs in a nonempty finset `S`, with `|S| - 1` gates. -/
private theorem bld_anyFinset {n : ℕ} {P : (Fin n → Bool) → Prop} (S : Finset (Fin n)) (hS : S.Nonempty) :
    Bld P (fun x => decide (∃ v ∈ S, x v = true)) (S.card - 1) := by
  obtain ⟨v, vs, hl⟩ : ∃ v vs, S.toList = v :: vs := by
    cases h : S.toList with
    | nil => simp at h; exact absurd h hS.ne_empty
    | cons v vs => exact ⟨v, vs, rfl⟩
  have hc : S.card = vs.length + 1 := by rw [← Finset.length_toList, hl]; rfl
  refine bld_congr (bld_mono (bld_anyList vs v) (by omega)) ?_
  intro x
  rw [Bool.eq_iff_iff, decide_eq_true_iff, ← hl, List.any_eq_true]
  simp

open Classical in
/-- The edge function of a nonempty set of edges `E` with a cover `T`. -/
private theorem bld_edges (n : ℕ) (P : (Fin n → Bool) → Prop) (T : Finset (Fin n)) : ∀ E : Finset (Sym2 (Fin n)), E.Nonempty →
    (∀ e ∈ E, ∃ t ∈ T, t ∈ e) →
    (∀ x, P x → ∀ e ∈ E, ¬ ∀ v ∈ e, x v = true) →
    Bld P (fun x => decide (∃ e ∈ E, ∀ v ∈ e, x v = true)) (E.card + T.card - 1) := by
  induction T using Finset.induction_on with
  | empty =>
    intro E hE hc hquiet
    obtain ⟨e, he⟩ := hE
    obtain ⟨t, ht, _⟩ := hc e he
    simp at ht
  | @insert t T0 htT ih =>
    intro E hE hc hquiet
    set E1 := E.filter (fun e => t ∈ e) with hE1
    set E2 := E.filter (fun e => t ∉ e) with hE2
    have hsplit : E1.card + E2.card = E.card := Finset.card_filter_add_card_filter_not _
    have hcard : (insert t T0).card = T0.card + 1 := Finset.card_insert_of_notMem htT
    have c2 : ∀ e ∈ E2, ∃ t' ∈ T0, t' ∈ e := by
      intro e he
      rw [hE2, Finset.mem_filter] at he
      obtain ⟨t', ht', hte⟩ := hc e he.1
      rcases Finset.mem_insert.1 ht' with h | h
      · subst h; exact absurd hte he.2
      · exact ⟨t', h, hte⟩
    -- the star at `t`
    set S := Finset.univ.filter (fun v : Fin n => s(t, v) ∈ E1) with hS
    have hSc : S.card ≤ E1.card := by
      refine Finset.card_le_card_of_injOn (fun v => s(t, v)) ?_ ?_
      · intro v hv
        simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hv
        exact hv
      · intro a _ b _ hab
        exact Sym2.congr_right.1 hab
    have star : E1.Nonempty → Bld P (fun x => decide (∃ e ∈ E1, ∀ v ∈ e, x v = true))
        E1.card := by
      intro h1
      have hSne : S.Nonempty := by
        obtain ⟨e, he⟩ := h1
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        exact ⟨b, by simp [hS, ← hb, he]⟩
      have quiet : ∀ x : Fin n → Bool, P x → (x t && decide (∃ v ∈ S, x v = true)) = false := by
        intro x hx
        apply Bool.eq_false_iff.mpr
        intro heq
        rw [Bool.and_eq_true, decide_eq_true_iff] at heq
        obtain ⟨xt,v,hv,xv⟩ := heq
        have he : s(t,v) ∈ E := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).2).1
        apply hquiet x hx s(t,v) he
        intro a ha
        rcases Sym2.mem_iff.mp ha with rfl | rfl <;> assumption
      have := bld_and (bld_var t) (bld_anyFinset S hSne) quiet
      have hpos := hSne.card_pos
      refine bld_congr (bld_mono this (by omega)) ?_
      intro x
      rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
      constructor
      · rintro ⟨ht, v, hv, hxv⟩
        refine ⟨s(t, v), (Finset.mem_filter.1 hv).2, ?_⟩
        intro u hu
        rcases Sym2.mem_iff.1 hu with rfl | rfl <;> assumption
      · rintro ⟨e, he, hall⟩
        have he' := he
        rw [hE1, Finset.mem_filter] at he'
        obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 he'.2
        subst hb
        exact ⟨hall t (Sym2.mem_mk_left _ _), b, by simp [hS, he],
          hall b (Sym2.mem_mk_right _ _)⟩
    have key : ∀ x : Fin n → Bool, decide (∃ e ∈ E, ∀ v ∈ e, x v = true)
        = (decide (∃ e ∈ E1, ∀ v ∈ e, x v = true) || decide (∃ e ∈ E2, ∀ v ∈ e, x v = true)) := by
      intro x
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_iff, hE1, hE2, Finset.mem_filter]
      constructor
      · rintro ⟨e, he, h⟩
        by_cases hte : t ∈ e
        · exact Or.inl ⟨e, ⟨he, hte⟩, h⟩
        · exact Or.inr ⟨e, ⟨he, hte⟩, h⟩
      · rintro (⟨e, ⟨he, _⟩, h⟩ | ⟨e, ⟨he, _⟩, h⟩) <;> exact ⟨e, he, h⟩
    rw [hcard]
    by_cases h1 : E1.Nonempty
    · by_cases h2 : E2.Nonempty
      · have := bld_or (star h1) (ih E2 h2 c2 (fun x hx e he => hquiet x hx e (Finset.mem_filter.mp he).1))
        have hp := h2.card_pos
        refine bld_congr (bld_mono this (by omega)) ?_
        intro x
        rw [key]
      · rw [Finset.not_nonempty_iff_eq_empty] at h2
        refine bld_congr (bld_mono (star h1) (by omega)) ?_
        intro x
        rw [key, h2]
        simp
    · rw [Finset.not_nonempty_iff_eq_empty] at h1
      have h2 : E2.Nonempty := by
        by_contra h2
        rw [Finset.not_nonempty_iff_eq_empty] at h2
        have := hE.card_pos
        rw [h1, h2] at hsplit
        simp at hsplit
        omega
      refine bld_congr (bld_mono (ih E2 h2 c2 (fun x hx e he => hquiet x hx e (Finset.mem_filter.mp he).1)) (by omega)) ?_
      intro x
      rw [key, h1]
      simp

private theorem extract {n : ℕ} {P : (Fin n → Bool) → Prop} {F : (Fin n → Bool) → Bool} {s : ℕ}
    (h : Bld P F s) : ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧
    D.size ≤ s ∧ circuitFun n D = F ∧ ∀ x : Fin n → Bool, P x → ∀ j < D.gates.length,
      (NestedCover.gateAt D j).op = .and → (D.wires (List.ofFn x)).getD (n+j) false = false := by
  obtain ⟨gs, o, hl, _, ev⟩ := h n le_rfl
  let D : Circuit := ⟨gs,o⟩
  have nice (x : Fin n → Bool) := (ev (List.ofFn x) List.length_ofFn).1
  have props (x : Fin n → Bool) (j : ℕ) (hj : j < gs.length) := run_info (nice x) j hj
  have root (j : ℕ) (hj : j < gs.length) := props (fun _ => false) j hj
  refine ⟨D,?_,?_,hl,?_,?_⟩
  · intro g hg
    change g ∈ gs at hg
    obtain ⟨j,hj,eq⟩ := List.getElem_of_mem hg
    have hg' : gs.getD j ⟨.or,[]⟩ = g := (List.getD_eq_getElem _ _ hj).trans eq
    have rule : allowed (gs.getD j ⟨.or,[]⟩) := (root j hj).1
    rw [hg'] at rule
    simpa [allowed] using rule
  · intro j hj i hi
    simpa only [List.length_ofFn] using (root j hj).2.1 i hi
  · funext x
    change (wiresFrom gs (List.ofFn x)).getD o false = F x
    simpa [getD_ofFn] using (ev (List.ofFn x) List.length_ofFn).2
  · intro x hx j hj hop
    have eq : (fun i : Fin n => (List.ofFn x).getD i false) = x := by funext i; exact getD_ofFn n x false i
    change (wiresFrom gs (List.ofFn x)).getD (n+j) false = false
    simpa only [List.length_ofFn] using (props x j hj).2.2 (by rwa [eq]) hop

open Classical in
/-- One center AND per nonempty star computes the edge function. Every such gate is off on every independent input. -/
theorem coverCircuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (T : Finset (Fin n))
    (edge : ∃ i j, G.Adj i j) (cov : ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧
      D.size ≤ G.edgeFinset.card + T.card - 1 ∧
      circuitFun n D = (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ x : Fin n → Bool, (¬ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
        ∀ j < D.gates.length, (NestedCover.gateAt D j).op = .and →
        (D.wires (List.ofFn x)).getD (n+j) false = false := by
  let P (x : Fin n → Bool) := ¬ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true
  obtain ⟨i,j,hij⟩ := edge
  have ne : G.edgeFinset.Nonempty := ⟨s(i,j), by simpa using hij⟩
  have hit : ∀ e ∈ G.edgeFinset, ∃ t ∈ T, t ∈ e := by
    intro e
    refine Sym2.ind (fun a b => ?_) e
    intro he
    rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
    rcases cov a b he with h | h
    · exact ⟨_,h,Sym2.mem_mk_left _ _⟩
    · exact ⟨_,h,Sym2.mem_mk_right _ _⟩
  have equiv (x : Fin n → Bool) : (∃ e ∈ G.edgeFinset, ∀ v ∈ e, x v = true) ↔
      ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true := by
    constructor
    · rintro ⟨e,he,h⟩
      revert he h
      refine Sym2.ind (fun a b => ?_) e
      intro he h
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he
      exact ⟨a,b,he,h a (Sym2.mem_mk_left _ _), h b (Sym2.mem_mk_right _ _)⟩
    · rintro ⟨a,b,hab,ha,hb⟩
      refine ⟨s(a,b), by simpa using hab, ?_⟩
      intro v hv
      rcases Sym2.mem_iff.mp hv with rfl | rfl <;> assumption
  apply extract (P := P)
  apply bld_congr (bld_edges n P T G.edgeFinset ne hit (fun x hx e he hv => hx ((equiv x).mp ⟨e,he,hv⟩)))
  intro x; rw [decide_eq_decide]; exact equiv x

end PEqualNP.Research.ForestNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.ForestNormal

/-- On every forest and every graph with long threads, a circuit of no greater size can be chosen
    with each AND silent on every independent input. The starting circuit may use NOT gates. -/
theorem PEqualNP.Research.ForestNormal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (classOfGraph : G.IsAcyclic ∨
      ((∀ (u : Fin n) (p : G.Walk u u), p.IsCycle → 7 ≤ p.length) ∧
       (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
        ∀ p : G.Walk u v, 7 ≤ p.length)))
    (C : Circuit) (basis : FanInTwo C)
    (computes : ∀ x : Fin n → Bool, circuitFun n C x = true ↔
      ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool, circuitFun n D x = true ↔
        ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) ∧
      (∀ x : Fin n → Bool, (¬ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) →
        ∀ j < D.gates.length, (NestedCover.gateAt D j).op = .and →
          (D.wires (List.ofFn x)).getD (n+j) false = false) := by
  classical
  by_cases edge : ∃ i j, G.Adj i j
  · let covers (S : Finset (Fin n)) := ∀ i j, G.Adj i j → i ∈ S ∨ j ∈ S
    have existsCov : ∃ k : ℕ, ∃ S : Finset (Fin n), covers S ∧ S.card = k :=
      ⟨_, Finset.univ, by intro i j _; exact Or.inl (Finset.mem_univ i), rfl⟩
    let k := Nat.find existsCov
    obtain ⟨T,hT,hcard⟩ := Nat.find_spec existsCov
    have minimal (S : Finset (Fin n)) (hS : covers S) : k ≤ S.card :=
      Nat.find_min' existsCov ⟨S,hS,rfl⟩
    have costs : HasCircuitSize n (fun x => decide (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)) C.size := by
      refine ⟨C,basis,le_rfl,?_⟩
      intro x
      rw [Bool.eq_iff_iff, decide_eq_true_iff]
      exact computes x
    have budget : G.edgeFinset.card + k ≤ C.size + 1 := by
      rcases classOfGraph with forest | ⟨girth,hubs⟩
      · exact L104 n k C.size G forest edge minimal costs
      · have costs' : HasCircuitSize n (fun x : Fin n → Bool => @decide
            ((∃ a ∈ (∅ : Finset (Fin n)), x a = true) ∨ ∃ i j, G.Adj i j ∧ x i = true ∧ x j = true)
            (Classical.propDecidable _)) C.size := by simpa using costs
        have hh := L204 n k C.size G ∅ girth hubs (by simp) (Or.inr edge) minimal costs'
        simpa [SimpleGraph.edgeFinset_card, Set.ncard_eq_toFinset_card'] using hh
    obtain ⟨D,hd,hr,hs,ev,quiet⟩ := coverCircuit n G T edge hT
    refine ⟨D, hd, hr, by change T.card = k at hcard; omega, ?_, quiet⟩
    intro x; rw [ev,decide_eq_true_iff]
  · let D : Circuit := ⟨[],n⟩
    refine ⟨D, by intro g hg; simp [D] at hg, by intro j hj; simp [D] at hj, Nat.zero_le _, ?_, ?_⟩
    · intro x
      have out : circuitFun n D x = false := by
        change (List.ofFn x).getD n false = false
        exact List.getD_eq_default _ _ (by simp)
      rw [out]; constructor
      · simp
      · rintro ⟨i,j,hij,_,_⟩; exact (edge ⟨i,j,hij⟩).elim
    · intro x hx j hj; simp [D] at hj
