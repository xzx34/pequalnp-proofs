import PEqualNP.Research.ForestNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Every forest incidence relation admits a no-larger circuit with all ANDs silent at singletons. -/
theorem PEqualNP.Research.ForestIncidence (N : ℕ) (I : Fin N → Fin N → Prop)
    (forest : (SimpleGraph.fromRel (fun a b : Fin (N+N) => ∃ p l : Fin N, I p l ∧ a = Fin.castAdd N p ∧ b = Fin.natAdd N l)).IsAcyclic) (C : Circuit) (hC : Monotone2 C)
    (spec : ∀ z : Fin (N+N) → Bool, circuitFun (N+N) C z = true ↔
      ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N+N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N+N) → Bool, circuitFun (N+N) D z = true ↔
        ∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = .and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N+N) => decide (k = Fin.castAdd N p)))).getD (N+N+j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N+N) => decide (k = Fin.natAdd N l)))).getD (N+N+j) false = false) := by
  classical
  let G := (SimpleGraph.fromRel (fun a b : Fin (N+N) => ∃ p l : Fin N, I p l ∧ a = Fin.castAdd N p ∧ b = Fin.natAdd N l))
  have adj (x : Fin (N+N) → Bool) : (∃ i j, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ∃ p l, I p l ∧ x (Fin.castAdd N p) = true ∧ x (Fin.natAdd N l) = true := by
    constructor
    · rintro ⟨a,b,⟨_,h⟩,ha,hb⟩
      rcases h with ⟨p,l,e,rfl,rfl⟩ | ⟨p,l,e,rfl,rfl⟩
      · exact ⟨_,_,e,ha,hb⟩
      · exact ⟨_,_,e,hb,ha⟩
    · rintro ⟨p,l,e,hp,hl⟩
      have diff : Fin.castAdd N p ≠ Fin.natAdd N l := by
        intro h
        have bad := congrArg Fin.val h
        change p.val = N + l.val at bad
        omega
      exact ⟨_,_,⟨diff, Or.inl ⟨p,l,e,rfl,rfl⟩⟩,hp,hl⟩
  have basis : FanInTwo C := by
    intro g hg
    have ⟨kind,arity⟩ := hC g hg
    refine ⟨?_,arity⟩
    simp at kind ⊢; tauto
  obtain ⟨D,mono,reads,budget,funD,quiet⟩ := PEqualNP.Research.ForestNormal (N+N) G (Or.inl forest) C basis
    (fun x => (spec x).trans (adj x).symm)
  refine ⟨D,mono,reads,budget,fun x => (funD x).trans (adj x),?_⟩
  intro j hj hop
  have single (v : Fin (N+N)) : (D.wires (List.ofFn (fun k => decide (k = v)))).getD (N+N+j) false = false := by
    apply quiet _ _ j hj hop
    rintro ⟨a,b,hab,ha,hb⟩
    have ea : a = v := of_decide_eq_true ha
    have eb : b = v := of_decide_eq_true hb
    rw [ea,eb] at hab
    exact G.loopless.irrefl v hab
  exact ⟨fun p => single (Fin.castAdd N p), fun l => single (Fin.natAdd N l)⟩
