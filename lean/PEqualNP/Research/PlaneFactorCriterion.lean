import PEqualNP.Outside.L_meta_1977
import PEqualNP.Outside.L_meta_2395

namespace PEqualNP.Research.PlaneFactorCriterion

abbrev Point := Fin 13
abbrev D : Finset Point := {0,1,3,9}
abbrev inc (p w : Point) := p - w ∈ D
abbrev hit (A : Point → Point → Prop) (P W : Finset Point) := ∃ p ∈ P, ∃ w ∈ W, A p w
abbrev away (P : Finset Point) : Finset Point := Finset.univ.filter fun w => ∀ p ∈ P, ¬inc p w
abbrev generic (P : Finset Point) := (∀ v ∉ P, ∃ w ∈ away P, inc v w) ∧
  (¬∃ w, ∀ p ∈ P, inc p w) ∧ ¬∃ v, ∀ w ∈ away P, inc v w
abbrev capP (P : Finset Point) := ∀ w : Point, (P.filter fun p => inc p w).card ≤ 2
abbrev capW (W : Finset Point) := ∀ p : Point, (W.filter fun w => inc p w).card ≤ 2

private theorem complete (P W : Finset Point) (no : ∀ p ∈ P, ∀ w ∈ W, ¬inc p w)
    (pc : capP P) (wc : capW W) : ∃ Q, P ⊆ Q ∧ W ⊆ away Q ∧ generic Q := by
  have eqv : ∀ p w : Point, inc p w ↔ p = w ∨ p = w + 1 ∨ p = w + 3 ∨ p = w + 9 := by decide
  have found := PEqualNP.Outside.L_meta_2395 P W
  simp_rw [← eqv] at found
  obtain ⟨Q,sub,av,cl,nc,nl⟩ := found no pc wc
  refine ⟨Q,sub,fun w hw => Finset.mem_filter.mpr ⟨Finset.mem_univ _,av w hw⟩,?_,nc,?_⟩
  · intro v hv
    obtain ⟨w,wa,wi⟩ := cl v hv
    exact ⟨w,Finset.mem_filter.mpr ⟨Finset.mem_univ _,wa⟩,wi⟩
  · rintro ⟨v,hv⟩
    exact nl ⟨v,fun w hw => hv w (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩)⟩

private theorem arcs (Q : Finset Point) (g : generic Q) : capP Q ∧ capW (away Q) := by
  have off {p w : Point} (hp : p ∈ Q) (hw : w ∈ away Q) : ¬inc p w := (Finset.mem_filter.mp hw).2 p hp
  have tr := PEqualNP.Outside.L_meta_1977
  have dual (a b : Point) : -a - -b = b - a := by abel
  constructor
  · intro k
    by_contra! large
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp large
    obtain ⟨z,hz⟩ := tr a b c k ab ac bc (Finset.mem_filter.mp ha).2
      (Finset.mem_filter.mp hb).2 (Finset.mem_filter.mp hc).2
    apply g.2.2
    exact ⟨z,fun w hw => hz w (off (Finset.mem_filter.mp ha).1 hw)
      (off (Finset.mem_filter.mp hb).1 hw) (off (Finset.mem_filter.mp hc).1 hw)⟩
  · intro k
    by_contra! large
    obtain ⟨a,b,c,ha,hb,hc,ab,ac,bc⟩ := Finset.two_lt_card_iff.mp large
    obtain ⟨z,hz⟩ := tr (-a) (-b) (-c) (-k) (fun e => ab (neg_injective e))
      (fun e => ac (neg_injective e)) (fun e => bc (neg_injective e))
      (by rw [dual]; exact (Finset.mem_filter.mp ha).2)
      (by rw [dual]; exact (Finset.mem_filter.mp hb).2)
      (by rw [dual]; exact (Finset.mem_filter.mp hc).2)
    apply g.2.1
    refine ⟨-z, fun p hp => ?_⟩
    have wi := hz (-p) (by rw [dual]; exact off hp (Finset.mem_filter.mp ha).1)
      (by rw [dual]; exact off hp (Finset.mem_filter.mp hb).1)
      (by rw [dual]; exact off hp (Finset.mem_filter.mp hc).1)
    simpa only [inc,sub_neg_eq_add,add_comm] using wi

end PEqualNP.Research.PlaneFactorCriterion

open PEqualNP.Research.PlaneFactorCriterion in
/-- Rejection of all generic maximal negatives by an intersection of bipartite edge functions
    is equivalent to the incidence condition on every transversal whose sides are arcs. -/
theorem PEqualNP.Research.PlaneFactorCriterion :
    let I (p w : Fin 13) := p - w ∈ ({0,1,3,9} : Finset (Fin 13))
    let F (P : Finset (Fin 13)) := Finset.univ.filter fun w => ∀ p ∈ P, ¬I p w
    let G (P : Finset (Fin 13)) := (∀ v ∉ P, ∃ w ∈ F P, I v w) ∧ (¬∃ w, ∀ p ∈ P, I p w) ∧
      ¬∃ v, ∀ w ∈ F P, I v w
    ∀ (m : ℕ) (A : Fin m → Fin 13 → Fin 13 → Prop),
      (∀ Q, G Q → ¬(∀ i, ∃ p ∈ Q, ∃ w ∈ F Q, A i p w)) ↔
      ∀ p w : Fin m → Fin 13, (∀ i, A i (p i) (w i)) →
        (∀ l, ((Finset.univ.image p).filter fun u => I u l).card ≤ 2) →
        (∀ v, ((Finset.univ.image w).filter fun l => I v l).card ≤ 2) →
        ∃ i j, I (p i) (w j) := by
  dsimp only
  intro m A
  constructor
  · intro sound p w h hp hw
    by_contra no
    obtain ⟨Q,inP,inW,g⟩ := complete (Finset.univ.image p) (Finset.univ.image w) (by
      rintro _ hi _ hj incij
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hj
      exact no ⟨i,j,incij⟩) hp hw
    apply sound Q g
    exact fun i => ⟨p i,inP (Finset.mem_image_of_mem _ (Finset.mem_univ _)),
      w i,inW (Finset.mem_image_of_mem _ (Finset.mem_univ _)),h i⟩
  · intro cross Q g all
    choose p hp w hw edge using all
    have subP : Finset.univ.image p ⊆ Q := Finset.image_subset_iff.mpr fun i _ => hp i
    have subW : Finset.univ.image w ⊆ away Q := Finset.image_subset_iff.mpr fun i _ => hw i
    obtain ⟨pc,wc⟩ := arcs Q g
    obtain ⟨i,j,on⟩ := cross p w edge
      (fun l => (Finset.card_le_card (Finset.filter_subset_filter _ subP)).trans (pc l))
      (fun i => (Finset.card_le_card (Finset.filter_subset_filter _ subW)).trans (wc i))
    exact (Finset.mem_filter.mp (hw j)).2 (p i) (hp i) on
