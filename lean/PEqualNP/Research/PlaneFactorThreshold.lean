import PEqualNP.Outside.L_meta_2395

namespace PEqualNP.Research.PlaneFactorThreshold

abbrev Point := Fin 13

abbrev Relation := Point → Point → Prop

abbrev inc (p w : Point) : Prop := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9

def hit (A : Relation) (P W : Finset Point) : Prop := ∃ p ∈ P, ∃ w ∈ W, A p w

def away (P : Finset Point) : Finset Point := Finset.univ.filter fun w => ∀ p ∈ P, ¬inc p w

def generic (P : Finset Point) : Prop :=
  (∀ v ∉ P, ∃ w ∈ away P, inc v w) ∧ (¬∃ w, ∀ p ∈ P, inc p w) ∧
    ¬∃ v, ∀ w ∈ away P, inc v w

private theorem avoids (P : Finset Point) : ¬hit inc P (away P) := by
  rintro ⟨p,hp,w,hw,hi⟩
  exact (Finset.mem_filter.mp hw).2 p hp hi

private theorem completePair (P W : Finset Point) (smallP : P.card ≤ 2) (smallW : W.card ≤ 2)
    (miss : ¬hit inc P W) : ∃ Q, P ⊆ Q ∧ W ⊆ away Q ∧ generic Q := by
  have indep : ∀ p ∈ P, ∀ w ∈ W, ¬inc p w := fun p hp w hw h => miss ⟨p,hp,w,hw,h⟩
  obtain ⟨Q,inQ,av,cl,nc,nl⟩ := PEqualNP.Outside.L_meta_2395 P W indep
    (fun j => (Finset.card_filter_le _ _).trans smallP) (fun j => (Finset.card_filter_le _ _).trans smallW)
  refine ⟨Q,inQ,fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _,av w hw⟩,?_,nc,?_⟩
  · intro v hv
    obtain ⟨w,wa,wi⟩ := cl v hv
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,wa⟩,wi⟩
  · rintro ⟨v,hv⟩
    exact nl ⟨v,fun w hw => hv w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)⟩

private theorem two (A B : Relation) (base : ∀ p w, inc p w → A p w ∧ B p w)
    (sound : ∀ Q, generic Q → ¬(hit A Q (away Q) ∧ hit B Q (away Q))) :
    ∀ P W, (hit A P W ∧ hit B P W) ↔ hit inc P W := by
  intro P W
  constructor
  · rintro ⟨⟨p,hp,w,hw,ha⟩,q,hq,l,hl,hb⟩
    by_contra no
    have mini : ¬hit inc {p,q} {w,l} := by
      rintro ⟨i,hi,j,hj,I⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      exact no ⟨i,hi.elim (fun h => h ▸ hp) (fun h => h ▸ hq),j,
        hj.elim (fun h => h ▸ hw) (fun h => h ▸ hl),I⟩
    have cardPair (a b : Point) : ({a,b} : Finset Point).card ≤ 2 := by
      calc _ ≤ ({b} : Finset Point).card + 1 := Finset.card_insert_le ..
           _ = _ := by simp
    obtain ⟨Q,inQ,inL,genericQ⟩ := completePair {p,q} {w,l} (cardPair ..) (cardPair ..) mini
    exact sound Q genericQ ⟨⟨p,inQ (by simp),w,inL (by simp),ha⟩,
      q,inQ (by simp),l,inL (by simp),hb⟩
  · rintro ⟨p,hp,w,hw,h⟩
    exact ⟨⟨p,hp,w,hw,(base p w h).1⟩,p,hp,w,hw,(base p w h).2⟩

private def plus (v : Point) : Relation := fun p w => inc p w ∨ (p = v ∧ w = 6)

private theorem three :
    ∃ A B D : Relation, (∀ p w, inc p w → A p w ∧ B p w ∧ D p w) ∧
      (∀ Q, generic Q → ¬(hit A Q (away Q) ∧ hit B Q (away Q) ∧ hit D Q (away Q))) ∧
      ∃ P W, hit A P W ∧ hit B P W ∧ hit D P W ∧ ¬hit inc P W := by
  refine ⟨plus 0, plus 1, plus 3, fun _ _ h => ⟨Or.inl h,Or.inl h,Or.inl h⟩,?_,?_⟩
  · rintro Q ⟨_,_,noPencil⟩ ⟨a,b,c⟩
    have contains (v : Point) (hv : hit (plus v) Q (away Q)) : v ∈ Q := by
      obtain ⟨p,hp,w,hw,h⟩ := hv
      rcases h with I | ⟨rfl,_⟩
      · exact False.elim (avoids Q ⟨p,hp,w,hw,I⟩)
      · exact hp
    have pencil : ∀ w : Point, ¬inc 0 w → ¬inc 1 w → ¬inc 3 w → inc 9 w := by decide
    apply noPencil
    refine ⟨9, fun w hw => ?_⟩
    have off := (Finset.mem_filter.mp hw).2
    exact pencil w (off _ (contains _ a)) (off _ (contains _ b)) (off _ (contains _ c))
  · refine ⟨{0,1,3},{6},⟨0,by simp,6,by simp,Or.inr ⟨rfl,rfl⟩⟩,
      ⟨1,by simp,6,by simp,Or.inr ⟨rfl,rfl⟩⟩,⟨3,by simp,6,by simp,Or.inr ⟨rfl,rfl⟩⟩,?_⟩
    unfold hit
    decide

end PEqualNP.Research.PlaneFactorThreshold

open PEqualNP.Research.PlaneFactorThreshold in
/-- Two bipartite edge functions that jointly fit the generic promise on the order-three plane
    already compute the complete incidence function. Three edge functions need not do so. -/
theorem PEqualNP.Research.PlaneFactorThreshold :
    let I (p w : Fin 13) := p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9
    let H (A : Fin 13 → Fin 13 → Prop) (P W : Finset (Fin 13)) := ∃ p ∈ P, ∃ w ∈ W, A p w
    let F (P : Finset (Fin 13)) := Finset.univ.filter fun w => ∀ p ∈ P, ¬I p w
    let G (P : Finset (Fin 13)) := (∀ v ∉ P, ∃ w ∈ F P, I v w) ∧ (¬∃ w, ∀ p ∈ P, I p w) ∧
      ¬∃ v, ∀ w ∈ F P, I v w
    (∀ A B, (∀ p w, I p w → A p w ∧ B p w) →
      (∀ Q, G Q → ¬(H A Q (F Q) ∧ H B Q (F Q))) →
      ∀ P W, (H A P W ∧ H B P W) ↔ H I P W) ∧
    ∃ A B D, (∀ p w, I p w → A p w ∧ B p w ∧ D p w) ∧
      (∀ Q, G Q → ¬(H A Q (F Q) ∧ H B Q (F Q) ∧ H D Q (F Q))) ∧
      ∃ P W, H A P W ∧ H B P W ∧ H D P W ∧ ¬H I P W := by
  exact ⟨two, three⟩
