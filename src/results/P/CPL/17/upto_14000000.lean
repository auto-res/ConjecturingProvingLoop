import Mathlib
import Aesop

namespace Topology

variable {X : Type*} [TopologicalSpace X]

def P1 (A : Set X) : Prop :=
  A ⊆ closure (interior A)

def P2 (A : Set X) : Prop :=
  A ⊆ interior (closure (interior A))

def P3 (A : Set X) : Prop :=
  A ⊆ interior (closure A)


theorem P2_implies_P1 {X : Type*} [TopologicalSpace X] (A : Set X) : P2 A → P1 A := by
  intro hP2
  intro x hxA
  exact
    (interior_subset :
      interior (closure (interior A)) ⊆ closure (interior A)) (hP2 hxA)

theorem P2_implies_P3 {X : Type*} [TopologicalSpace X] (A : Set X) : P2 A → P3 A := by
  intro hP2
  intro x hxA
  have hsubset : interior (closure (interior A)) ⊆ interior (closure A) := by
    have : closure (interior A) ⊆ closure A := closure_mono interior_subset
    exact interior_mono this
  exact hsubset (hP2 hxA)

theorem interior_closure_interior_subset_closure {X : Type*} [TopologicalSpace X] (A : Set X) : interior (closure (interior A)) ⊆ closure A := by
  intro x hx
  have h₁ : x ∈ interior (closure A) := by
    have hmono : closure (interior A) ⊆ closure A := closure_mono interior_subset
    have hsubset : interior (closure (interior A)) ⊆ interior (closure A) :=
      interior_mono hmono
    exact hsubset hx
  exact (interior_subset : interior (closure A) ⊆ closure A) h₁

theorem P3_iff_exists_open_superset {X : Type*} [TopologicalSpace X] (A : Set X) : P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, ?_, interior_subset⟩
    exact hP3
  · rintro ⟨U, hU_open, hA_sub_U, hU_sub_closure⟩
    intro x hxA
    have hxU : x ∈ U := hA_sub_U hxA
    have hU_sub_int : U ⊆ interior (closure A) :=
      interior_maximal hU_sub_closure hU_open
    exact hU_sub_int hxU

theorem P1_iff_closure_eq_closure_interior {X : Type*} [TopologicalSpace X] (A : Set X) : P1 A ↔ closure A = closure (interior A) := by
  constructor
  · intro hP1
    apply subset_antisymm
    · -- `closure A ⊆ closure (interior A)`
      have hclosed : IsClosed (closure (interior A)) := isClosed_closure
      exact closure_minimal hP1 hclosed
    · -- `closure (interior A) ⊆ closure A`
      exact closure_mono interior_subset
  · intro hEq
    -- need to show `A ⊆ closure (interior A)`
    intro x hxA
    have hx_closure : x ∈ closure A := subset_closure hxA
    simpa [hEq] using hx_closure

theorem P3_univ {X : Type*} [TopologicalSpace X] : P3 (Set.univ : Set X) := by
  intro x hx
  simpa using hx

theorem P1_empty {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P2_empty {X : Type*} [TopologicalSpace X] : P2 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P3_empty {X : Type*} [TopologicalSpace X] : P3 (∅ : Set X) := by
  exact Set.empty_subset _

theorem P1_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P1 A → Topology.P1 B → Topology.P1 (A ∪ B) := by
  intro hPA hPB
  intro x hx
  cases hx with
  | inl hxA =>
      -- x ∈ A
      have hx_closureA : x ∈ closure (interior A) := hPA hxA
      have hsubset : closure (interior A) ⊆ closure (interior (A ∪ B)) := by
        have hsub_interior : interior A ⊆ interior (A ∪ B) := by
          have h : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono h
        exact closure_mono hsub_interior
      exact hsubset hx_closureA
  | inr hxB =>
      -- x ∈ B
      have hx_closureB : x ∈ closure (interior B) := hPB hxB
      have hsubset : closure (interior B) ⊆ closure (interior (A ∪ B)) := by
        have hsub_interior : interior B ⊆ interior (A ∪ B) := by
          have h : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono h
        exact closure_mono hsub_interior
      exact hsubset hx_closureB

theorem exists_open_between_P1_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P3 A → ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ closure A := by
  intro _ hP3
  exact (P3_iff_exists_open_superset (X := X) (A := A)).1 hP3

theorem P2_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P2 A → Topology.P2 B → Topology.P2 (A ∪ B) := by
  intro hP2A hP2B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_in : x ∈ interior (closure (interior A)) := hP2A hxA
      have hsubset :
          interior (closure (interior A)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_int : interior A ⊆ interior (A ∪ B) := by
          have h : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact interior_mono h
        have h_closure : closure (interior A) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int
        exact interior_mono h_closure
      exact hsubset hx_in
  | inr hxB =>
      have hx_in : x ∈ interior (closure (interior B)) := hP2B hxB
      have hsubset :
          interior (closure (interior B)) ⊆
            interior (closure (interior (A ∪ B))) := by
        have h_int : interior B ⊆ interior (A ∪ B) := by
          have h : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact interior_mono h
        have h_closure : closure (interior B) ⊆ closure (interior (A ∪ B)) :=
          closure_mono h_int
        exact interior_mono h_closure
      exact hsubset hx_in

theorem P2_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} : P2 A → P2 (e '' A) := by
  intro hP2
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  have hx : x ∈ interior (closure (interior A)) := hP2 hxA
  have hmem : (e x) ∈ (e '' interior (closure (interior A))) := ⟨x, hx, rfl⟩
  have h1 : (e x) ∈ interior (e '' closure (interior A)) := by
    simpa [e.image_interior (closure (interior A))] using hmem
  have h2 : (e x) ∈ interior (closure (e '' interior A)) := by
    simpa [e.image_closure (interior A)] using h1
  have h3 : (e x) ∈ interior (closure (interior (e '' A))) := by
    simpa [e.image_interior A] using h2
  exact h3

theorem exists_P1_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ P1 B := by
  refine ⟨interior A, interior_subset, ?_⟩
  intro x hx
  have : x ∈ closure (interior A) := subset_closure hx
  simpa [interior_interior] using this

theorem P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P2 A := by
  intro x hxA
  -- Since `A` is open, its interior is `A` itself.
  have hInt : interior A = A := hA.interior_eq
  -- Hence `x` belongs to `interior A`.
  have hxInt : x ∈ interior A := by
    simpa [hInt] using hxA
  -- `interior A` is contained in `interior (closure A)`.
  have hxIntClosure : x ∈ interior (closure A) :=
    (interior_mono (subset_closure : (A : Set X) ⊆ closure A)) hxInt
  -- `closure (interior A)` coincides with `closure A`.
  have hClosure : closure (interior A) = closure A := by
    simpa [hInt]
  -- Rewriting with this equality gives the desired conclusion.
  simpa [hClosure] using hxIntClosure

theorem P1_interior {X : Type*} [TopologicalSpace X] (A : Set X) : P1 (interior A) := by
  intro x hx
  simpa [interior_interior] using (subset_closure hx)

theorem P2_interior {X : Type*} [TopologicalSpace X] (A : Set X) : P2 (interior A) := by
  intro x hx
  have hsubset : interior A ⊆ interior (closure (interior A)) :=
    interior_maximal (subset_closure : (interior A) ⊆ closure (interior A)) isOpen_interior
  have hx' : x ∈ interior (closure (interior A)) := hsubset hx
  simpa [interior_interior] using hx'

theorem P1_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} : P1 A → P1 (e '' A) := by
  intro hP1
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- `x` satisfies `P1`, hence it is in the closure of the interior of `A`
  have hx : x ∈ closure (interior A) := hP1 hxA
  -- Map this membership through the homeomorphism
  have hmem : (e x) ∈ (e '' closure (interior A)) := ⟨x, hx, rfl⟩
  -- Use the fact that a homeomorphism maps closures to closures
  have h1 : (e x) ∈ closure (e '' interior A) := by
    simpa [e.image_closure (interior A)] using hmem
  -- And interiors to interiors
  have h2 : (e x) ∈ closure (interior (e '' A)) := by
    simpa [e.image_interior A] using h1
  exact h2

theorem P3_image_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {A : Set X} : P3 A → P3 (e '' A) := by
  intro hP3
  intro y hy
  rcases hy with ⟨x, hxA, rfl⟩
  -- Using `P3` for `A`
  have hx : x ∈ interior (closure A) := hP3 hxA
  -- Map the point through the homeomorphism
  have hmem : (e x) ∈ (e '' interior (closure A)) := ⟨x, hx, rfl⟩
  -- Convert the image of the interior
  have h1 : (e x) ∈ interior (e '' closure A) := by
    simpa [e.image_interior (closure A)] using hmem
  -- Convert the image of the closure
  have h2 : (e x) ∈ interior (closure (e '' A)) := by
    simpa [e.image_closure A] using h1
  exact h2

theorem P3_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P3 (Aᶜ) := by
  intro x hx
  -- `Aᶜ` is open because `A` is closed
  have h_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  -- Since `Aᶜ` is open, its interior is itself
  have hx_int : x ∈ interior (Aᶜ) := by
    have h_eq : interior (Aᶜ) = Aᶜ := h_open.interior_eq
    simpa [h_eq] using hx
  -- The interior of a set is contained in the interior of its closure
  have hsubset : interior (Aᶜ) ⊆ interior (closure (Aᶜ)) :=
    interior_mono (subset_closure : (Aᶜ : Set X) ⊆ closure (Aᶜ))
  exact hsubset hx_int

theorem exists_P3_superset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, A ⊆ B ∧ P3 B := by
  exact ⟨Set.univ, Set.subset_univ A, P3_univ (X := X)⟩

theorem P2_implies_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → closure A = closure (interior A) := by
  intro hP2
  exact
    (P1_iff_closure_eq_closure_interior (A := A)).1
      (P2_implies_P1 (A := A) hP2)

theorem exists_P2_superset_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ B, A ⊆ B ∧ Topology.P2 B := by
  intro _hP1
  refine ⟨(Set.univ : Set X), Set.subset_univ _, ?_⟩
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P1_iUnion {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, Topology.P1 (f i)) → Topology.P1 (⋃ i, f i) := by
  intro hP1
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_closure : x ∈ closure (interior (f i)) := hP1 i hxi
  have hsubset : closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) := by
    have h_int_subset : interior (f i) ⊆ interior (⋃ j, f j) := by
      have h_subset : (f i : Set X) ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    exact closure_mono h_int_subset
  exact hsubset hx_closure

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 A → Topology.P3 B → Topology.P3 (Set.prod A B) := by
  intro hP3A hP3B
  intro p hp
  -- Split the point into its coordinates
  rcases p with ⟨x, y⟩
  -- Membership of the coordinates in `A` and `B`
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  -- Apply `P3` to get interior points of the closures
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  have hy_int : y ∈ interior (closure B) := hP3B hyB
  -- The open rectangle that contains `(x, y)`
  have h_mem_rect :
      (x, y) ∈ (interior (closure A)) ×ˢ (interior (closure B)) :=
    ⟨hx_int, hy_int⟩
  have h_rect_open :
      IsOpen ((interior (closure A)) ×ˢ (interior (closure B))) :=
    isOpen_interior.prod isOpen_interior
  -- Show the rectangle is contained in `closure (A ×ˢ B)`
  have h_rect_subset :
      (interior (closure A)) ×ˢ (interior (closure B)) ⊆
        closure (A ×ˢ B) := by
    intro q hq
    rcases hq with ⟨hq1, hq2⟩
    -- Each coordinate is in the respective closure
    have hq1_cl : q.1 ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hq1
    have hq2_cl : q.2 ∈ closure B :=
      (interior_subset : interior (closure B) ⊆ closure B) hq2
    -- Hence the point is in `closure A ×ˢ closure B`
    have hq_in : q ∈ (closure A) ×ˢ (closure B) := ⟨hq1_cl, hq2_cl⟩
    -- And `closure (A ×ˢ B)` coincides with that product
    have h_eq :
        closure (A ×ˢ B) = (closure A) ×ˢ (closure B) := by
      simpa using
        (closure_prod_eq :
          closure (A ×ˢ B) = (closure A) ×ˢ (closure B))
    simpa [h_eq] using hq_in
  -- An open set contained in a closure lies in the interior
  have h_rect_interior :
      (interior (closure A)) ×ˢ (interior (closure B)) ⊆
        interior (closure (A ×ˢ B)) :=
    interior_maximal h_rect_subset h_rect_open
  -- Finish
  exact h_rect_interior h_mem_rect

theorem P3_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P3 A → Topology.P3 B → Topology.P3 (A ∪ B) := by
  intro hP3A hP3B
  intro x hx
  cases hx with
  | inl hxA =>
      have hx_int : x ∈ interior (closure A) := hP3A hxA
      have hsubset : interior (closure A) ⊆ interior (closure (A ∪ B)) := by
        have hclosure : closure A ⊆ closure (A ∪ B) := by
          have h : (A : Set X) ⊆ A ∪ B := Set.subset_union_left
          exact closure_mono h
        exact interior_mono hclosure
      exact hsubset hx_int
  | inr hxB =>
      have hx_int : x ∈ interior (closure B) := hP3B hxB
      have hsubset : interior (closure B) ⊆ interior (closure (A ∪ B)) := by
        have hclosure : closure B ⊆ closure (A ∪ B) := by
          have h : (B : Set X) ⊆ A ∪ B := Set.subset_union_right
          exact closure_mono h
        exact interior_mono hclosure
      exact hsubset hx_int

theorem P3_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A := by
  intro x hxA
  -- Since `A` is open, its interior equals itself
  have hxInt : x ∈ interior A := by
    simpa [hA.interior_eq] using hxA
  -- The interior of `A` is contained in the interior of its closure
  have hsubset : interior A ⊆ interior (closure A) :=
    interior_mono (subset_closure : (A : Set X) ⊆ closure A)
  exact hsubset hxInt

theorem P2_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P2 A → Topology.P2 B → Topology.P2 (Set.prod A B) := by
  intro hP2A hP2B
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  have hy_int : y ∈ interior (closure (interior B)) := hP2B hyB
  -- Define the open rectangle containing `(x, y)`
  let R : Set (X × Y) :=
      (interior (closure (interior A))) ×ˢ
        (interior (closure (interior B)))
  have h_mem_R : (x, y) ∈ R := by
    dsimp [R]
    exact ⟨hx_int, hy_int⟩
  -- `R` is open
  have hR_open : IsOpen R := by
    dsimp [R]
    exact (isOpen_interior).prod isOpen_interior
  -- We will show `R ⊆ closure (interior (A ×ˢ B))`
  have hR_subset : R ⊆ closure (interior (A ×ˢ B)) := by
    intro q hqR
    dsimp [R] at hqR
    -- Put `q` in `closure ((interior A) ×ˢ (interior B))`
    have hq_prod :
        q ∈ (closure (interior A)) ×ˢ (closure (interior B)) := by
      exact
        ⟨ (interior_subset :
              interior (closure (interior A)) ⊆
                closure (interior A)) hqR.1,
          (interior_subset :
              interior (closure (interior B)) ⊆
                closure (interior B)) hqR.2 ⟩
    -- Identify this product with the closure of a product
    have h_closure_prod :
        closure ((interior A) ×ˢ (interior B)) =
          (closure (interior A)) ×ˢ (closure (interior B)) := by
      simpa using
        (closure_prod_eq :
          closure ((interior A) ×ˢ (interior B)) =
            (closure (interior A)) ×ˢ (closure (interior B)))
    have hq_in_closure_prod :
        q ∈ closure ((interior A) ×ˢ (interior B)) := by
      simpa [h_closure_prod] using hq_prod
    -- Show that this closure is contained in `closure (interior (A ×ˢ B))`
    have h_int_subset :
        (interior A) ×ˢ (interior B) ⊆ interior (A ×ˢ B) := by
      intro r hr
      -- The rectangle is open and contained in `A ×ˢ B`
      have h_open_rect : IsOpen ((interior A) ×ˢ (interior B)) :=
        (isOpen_interior).prod isOpen_interior
      have h_rect_subset :
          ((interior A) ×ˢ (interior B)) ⊆ A ×ˢ B := by
        intro s hs
        exact ⟨ (interior_subset : interior A ⊆ A) hs.1,
                (interior_subset : interior B ⊆ B) hs.2 ⟩
      have h_to_int :
          ((interior A) ×ˢ (interior B)) ⊆ interior (A ×ˢ B) :=
        interior_maximal h_rect_subset h_open_rect
      exact h_to_int hr
    have h_closure_mono :
        closure ((interior A) ×ˢ (interior B)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_int_subset
    exact h_closure_mono hq_in_closure_prod
  -- An open set contained in a closure lies inside its interior
  have hR_interior :
      R ⊆ interior (closure (interior (A ×ˢ B))) :=
    interior_maximal hR_subset hR_open
  exact hR_interior h_mem_R

theorem P3_iUnion {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, Topology.P3 (f i)) → Topology.P3 (⋃ i, f i) := by
  intro hP3
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (f i)) := hP3 i hxi
  have hsubset : interior (closure (f i)) ⊆ interior (closure (⋃ j, f j)) := by
    have h_closure_subset : closure (f i) ⊆ closure (⋃ j, f j) := by
      have h_subset : (f i : Set X) ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact closure_mono h_subset
    exact interior_mono h_closure_subset
  exact hsubset hx_int

theorem P1_existence_of_dense_open {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U, IsOpen U ∧ closure U = closure A := by
  intro hP1
  refine ⟨interior A, isOpen_interior, ?_⟩
  apply subset_antisymm
  ·
    exact closure_mono (interior_subset : (interior A) ⊆ A)
  ·
    have h_closed : IsClosed (closure (interior A)) := isClosed_closure
    exact closure_minimal hP1 h_closed

theorem P1_closure_interior_eq_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → closure (interior A) = closure A := by
  intro hP1
  simpa using ((P1_iff_closure_eq_closure_interior (A := A)).1 hP1).symm

theorem exists_dense_open_subset_of_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ U : Set X, IsOpen U ∧ closure U = closure A := by
  intro hP2
  refine ⟨interior A, isOpen_interior, ?_⟩
  simpa using (P2_implies_closure_eq (A := A) hP2).symm

theorem P2_iff_P1_and_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A ↔ Topology.P1 A ∧ Topology.P3 A := by
  constructor
  · intro hP2
    exact ⟨P2_implies_P1 (A := A) hP2, P2_implies_P3 (A := A) hP2⟩
  · rintro ⟨hP1, hP3⟩
    intro x hxA
    have hEq : closure A = closure (interior A) :=
      (P1_iff_closure_eq_closure_interior (A := A)).1 hP1
    have hx : x ∈ interior (closure A) := hP3 hxA
    simpa [hEq] using hx

theorem P3_of_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} (h : closure A ⊆ interior (closure A)) : Topology.P3 A := by
  intro x hxA
  exact h (subset_closure hxA)

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P1 A → Topology.P1 B → Topology.P1 (Set.prod A B) := by
  intro hP1A hP1B
  intro p hp
  rcases p with ⟨x, y⟩
  have hxA : x ∈ A := hp.1
  have hyB : y ∈ B := hp.2
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  have hy_cl : y ∈ closure (interior B) := hP1B hyB
  -- The point lies in the product of the two closures
  have h_mem :
      (x, y) ∈ (closure (interior A)) ×ˢ (closure (interior B)) :=
    ⟨hx_cl, hy_cl⟩
  -- This product is contained in the desired closure
  have h_subset :
      (closure (interior A)) ×ˢ (closure (interior B)) ⊆
        closure (interior (A ×ˢ B)) := by
    intro q hq
    -- First place `q` in `closure ((interior A) ×ˢ (interior B))`
    have hq_in :
        q ∈ closure ((interior A) ×ˢ (interior B)) := by
      -- Identify the two closures
      have h_eq :
          closure ((interior A) ×ˢ (interior B)) =
            (closure (interior A)) ×ˢ (closure (interior B)) := by
        simpa using
          (closure_prod_eq :
            closure ((interior A) ×ˢ (interior B)) =
              (closure (interior A)) ×ˢ (closure (interior B)))
      simpa [h_eq] using hq
    -- Show the latter closure is inside `closure (interior (A ×ˢ B))`
    have h_mono :
        (interior A) ×ˢ (interior B) ⊆ interior (A ×ˢ B) := by
      intro r hr
      -- The rectangle is open and contained in `A ×ˢ B`
      have h_open : IsOpen ((interior A) ×ˢ (interior B)) :=
        (isOpen_interior).prod isOpen_interior
      have h_sub :
          ((interior A) ×ˢ (interior B)) ⊆ A ×ˢ B := by
        intro s hs
        exact
          ⟨ (interior_subset : interior A ⊆ A) hs.1,
            (interior_subset : interior B ⊆ B) hs.2 ⟩
      exact (interior_maximal h_sub h_open) hr
    have h_closure_mono :
        closure ((interior A) ×ˢ (interior B)) ⊆
          closure (interior (A ×ˢ B)) :=
      closure_mono h_mono
    exact h_closure_mono hq_in
  -- Conclude
  exact h_subset h_mem

theorem P3_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} : Topology.P3 B → Topology.P3 (e ⁻¹' B) := by
  intro hP3B
  -- Transport `P3` through the inverse homeomorphism
  have hP3_image : Topology.P3 (e.symm '' B) :=
    (P3_image_homeomorph (e := e.symm) (A := B)) hP3B
  -- Identify the image by the inverse with the preimage by `e`
  have h_eq : (e.symm '' B) = (e ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ B
      simpa using hy
    · intro hx
      have hy : e x ∈ B := hx
      exact ⟨e x, hy, by
        simpa using e.symm_apply_apply x⟩
  -- Conclude via rewriting
  simpa [h_eq] using hP3_image

theorem P2_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P2 A := by
  intro x hxA
  -- In a subsingleton, any nonempty set is the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    ext y
    constructor
    · intro _; trivial
    · intro _
      have h_eq : y = x := Subsingleton.elim y x
      simpa [h_eq] using hxA
  -- The goal follows after rewriting with this fact.
  have : x ∈ interior (closure (interior A)) := by
    have hx_univ : x ∈ (Set.univ : Set X) := by
      trivial
    simpa [hA_univ, interior_univ, closure_univ] using hx_univ
  exact this

theorem P1_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} : (∀ A ∈ S, Topology.P1 A) → Topology.P1 (⋃₀ S) := by
  intro hP1
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hx_closure : x ∈ closure (interior A) := hP1 A hAS hxA
  have hsubset : closure (interior A) ⊆ closure (interior (⋃₀ S)) := by
    have h_int_subset : interior A ⊆ interior (⋃₀ S) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ S := Set.subset_sUnion_of_mem hAS
      exact interior_mono hA_subset
    exact closure_mono h_int_subset
  exact hsubset hx_closure

theorem P3_unionₛ {X : Type*} [TopologicalSpace X] {S : Set (Set X)} : (∀ A ∈ S, Topology.P3 A) → Topology.P3 (⋃₀ S) := by
  intro hP3
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hx_int : x ∈ interior (closure A) := hP3 A hAS hxA
  have hsubset : interior (closure A) ⊆ interior (closure (⋃₀ S)) := by
    have h_closure_subset : closure A ⊆ closure (⋃₀ S) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ S := Set.subset_sUnion_of_mem hAS
      exact closure_mono hA_subset
    exact interior_mono h_closure_subset
  exact hsubset hx_int

theorem P2_complement_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P2 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  exact P2_of_open (A := Aᶜ) h_open

theorem P3_iff_P2_for_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P3 A ↔ Topology.P2 A := by
  constructor
  · intro hP3
    -- `P3` together with closedness implies openness
    have h_subset : (A : Set X) ⊆ interior A := by
      intro x hx
      have hx_int_cl : x ∈ interior (closure A) := hP3 hx
      have h_closure : closure A = A := hA.closure_eq
      simpa [h_closure] using hx_int_cl
    have h_eq : interior A = A := by
      apply subset_antisymm
      · exact interior_subset
      · exact h_subset
    have h_open : IsOpen A := by
      simpa [h_eq] using (isOpen_interior : IsOpen (interior A))
    exact P2_of_open (A := A) h_open
  · intro hP2
    exact P2_implies_P3 (A := A) hP2

theorem P3_of_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : Topology.P3 A := by
  intro x hxA
  -- `closure A` is the whole space because `A` is dense
  have hClosure : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _
      simp
    · intro y _
      exact hA y
  -- hence its interior is also the whole space
  have hInterior : interior (closure A) = (Set.univ : Set X) := by
    simpa [hClosure, interior_univ]
  -- conclude
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hInterior] using this

theorem P2_iUnion {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, Topology.P2 (f i)) → Topology.P2 (⋃ i, f i) := by
  intro hP2
  intro x hx
  rcases Set.mem_iUnion.1 hx with ⟨i, hxi⟩
  have hx_int : x ∈ interior (closure (interior (f i))) := hP2 i hxi
  have hsubset :
      interior (closure (interior (f i))) ⊆
        interior (closure (interior (⋃ j, f j))) := by
    -- First, show `interior (f i)` is contained in `interior (⋃ j, f j)`.
    have h_int_subset : interior (f i) ⊆ interior (⋃ j, f j) := by
      have h_subset : (f i : Set X) ⊆ ⋃ j, f j := by
        intro y hy
        exact Set.mem_iUnion.2 ⟨i, hy⟩
      exact interior_mono h_subset
    -- Then, use monotonicity of `closure` and `interior`.
    have h_closure_subset :
        closure (interior (f i)) ⊆ closure (interior (⋃ j, f j)) :=
      closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact hsubset hx_int

theorem P2_sUnion {X : Type*} [TopologicalSpace X] {S : Set (Set X)} : (∀ A ∈ S, Topology.P2 A) → Topology.P2 (⋃₀ S) := by
  intro hP2
  intro x hx
  rcases Set.mem_sUnion.1 hx with ⟨A, hAS, hxA⟩
  have hx_int : x ∈ interior (closure (interior A)) := (hP2 A hAS) hxA
  have hsubset :
      interior (closure (interior A)) ⊆
        interior (closure (interior (⋃₀ S))) := by
    -- First, show `interior A ⊆ interior (⋃₀ S)`.
    have h_int_subset : interior A ⊆ interior (⋃₀ S) := by
      have hA_subset : (A : Set X) ⊆ ⋃₀ S := Set.subset_sUnion_of_mem hAS
      exact interior_mono hA_subset
    -- Then lift this inclusion through `closure` and `interior`.
    have h_closure_subset :
        closure (interior A) ⊆ closure (interior (⋃₀ S)) :=
      closure_mono h_int_subset
    exact interior_mono h_closure_subset
  exact hsubset hx_int

theorem exists_compact_P3_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K, IsCompact K ∧ K ⊆ A ∧ Topology.P3 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · exact P3_empty (X := X)

theorem P1_of_open {X : Type*} [TopologicalSpace X] {A : Set X} : IsOpen A → Topology.P1 A := by
  intro hA
  intro x hx
  have : x ∈ closure A := subset_closure hx
  simpa [hA.interior_eq] using this

theorem P1_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} : Topology.P1 B → Topology.P1 (e ⁻¹' B) := by
  intro hP1B
  -- Transport `P1` through the inverse homeomorphism
  have hP1_image : Topology.P1 (e.symm '' B) :=
    (P1_image_homeomorph (e := e.symm) (A := B)) hP1B
  -- Identify the image by the inverse with the preimage by `e`
  have h_eq : (e.symm '' B) = (e ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ B
      simpa using hy
    · intro hx
      have hy : e x ∈ B := hx
      exact ⟨e x, hy, by
        simpa using e.symm_apply_apply x⟩
  -- Conclude via rewriting
  simpa [h_eq] using hP1_image

theorem P2_preimage_homeomorph {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {e : X ≃ₜ Y} {B : Set Y} : Topology.P2 B → Topology.P2 (e ⁻¹' B) := by
  intro hP2B
  -- Transport `P2` through the inverse homeomorphism
  have hP2_image : Topology.P2 (e.symm '' B) :=
    (P2_image_homeomorph (e := e.symm) (A := B)) hP2B
  -- Identify the image by the inverse with the preimage by `e`
  have h_eq : (e.symm '' B) = (e ⁻¹' B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (e.symm y) ∈ B
      simpa using hy
    · intro hx
      have hy : e x ∈ B := hx
      exact ⟨e x, hy, by
        simpa using e.symm_apply_apply x⟩
  -- Conclude via rewriting
  simpa [h_eq] using hP2_image

theorem exists_compact_P2_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K, IsCompact K ∧ K ⊆ A ∧ Topology.P2 K := by
  refine ⟨(∅ : Set X), isCompact_empty, ?_, ?_⟩
  · exact Set.empty_subset _
  · exact P2_empty (X := X)

theorem P3_interior {X : Type*} [TopologicalSpace X] {A : Set X} : P3 (interior A) := by
  simpa using P3_of_open (A := interior A) isOpen_interior

theorem exists_P2_subset_dense {X : Type*} [TopologicalSpace X] {A : Set X} (hA : Dense A) : ∃ B, B ⊆ A ∧ P2 B := by
  refine ⟨interior A, interior_subset, ?_⟩
  exact P2_interior (X := X) (A := A)

theorem P3_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P3 A := by
  exact (P2_implies_P3 (A := A) (P2_subsingleton (A := A)))

theorem P3_of_compact_dense_interior {X : Type*} [TopologicalSpace X] {A : Set X} : IsCompact A → Dense (interior A) → Topology.P3 A := by
  intro _ hDense
  intro x hxA
  -- First, `closure (interior A)` is the whole space because `interior A` is dense.
  have h_closure_int : closure (interior A) = (Set.univ : Set X) := by
    simpa using hDense.closure_eq
  -- Hence `closure A` is also the whole space.
  have h_closureA : closure A = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro y _; trivial
    ·
      have : closure (interior A) ⊆ closure A :=
        closure_mono (interior_subset : (interior A : Set X) ⊆ A)
      simpa [h_closure_int] using this
  -- Therefore its interior is the whole space.
  have h_interior : interior (closure A) = (Set.univ : Set X) := by
    simpa [h_closureA, interior_univ]
  -- Conclude that every point of `A` lies in that interior.
  have : x ∈ (Set.univ : Set X) := by
    trivial
  simpa [h_interior] using this

theorem P3_iff_P1_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P3 A ↔ Topology.P1 A := by
  constructor
  · intro _hP3
    exact P1_of_open (A := A) hA
  · intro _hP1
    exact P3_of_open (A := A) hA

theorem P2_iff_P3_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A ↔ Topology.P3 A := by
  constructor
  · intro hP2
    exact P2_implies_P3 (A := A) hP2
  · intro _hP3
    exact P2_of_open (A := A) hA

theorem exists_open_P2_superset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure A) := by
  intro hP2
  have hP3 : P3 A := P2_implies_P3 (A := A) hP2
  refine ⟨interior (closure A), isOpen_interior, ?_, subset_rfl⟩
  exact hP3

theorem P1_subsingleton {X : Type*} [TopologicalSpace X] [Subsingleton X] (A : Set X) : Topology.P1 A := by
  exact (P2_implies_P1 (A := A)) (P2_subsingleton (A := A))

theorem P1_univ {X : Type*} [TopologicalSpace X] : Topology.P1 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_univ {X : Type*} [TopologicalSpace X] : Topology.P2 (Set.univ : Set X) := by
  intro x hx
  simpa [interior_univ, closure_univ] using hx

theorem P2_iff_P1_for_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : Topology.P2 A ↔ Topology.P1 A := by
  constructor
  · intro hP2
    exact P2_implies_P1 (A := A) hP2
  · intro _hP1
    exact P2_of_open (A := A) hA

theorem exists_dense_P1_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ B, A ⊆ B ∧ Dense B ∧ Topology.P1 B := by
  refine ⟨(Set.univ : Set X), Set.subset_univ _, dense_univ, P1_univ (X := X)⟩

theorem P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P2 A → A = interior A := by
  intro hA_closed hP2A
  apply Set.Subset.antisymm
  · intro x hxA
    have hx_mem : x ∈ interior (closure (interior A)) := hP2A hxA
    have h_subset : interior (closure (interior A)) ⊆ interior A := by
      -- First, establish `closure (interior A) ⊆ A`.
      have h_closure_subset : closure (interior A) ⊆ A := by
        have h_int_subset : (interior A : Set X) ⊆ A := interior_subset
        have h_closure_subset' : closure (interior A) ⊆ closure A :=
          closure_mono h_int_subset
        simpa [hA_closed.closure_eq] using h_closure_subset'
      -- Use monotonicity of interior to get the desired inclusion.
      exact interior_mono h_closure_subset
    exact h_subset hx_mem
  · exact interior_subset

theorem P1_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P1 A → Topology.P1 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP1A
  have hP1_univ : Topology.P1 (Set.univ : Set Y) := P1_univ (X := Y)
  simpa using (P1_prod (A := A) (B := (Set.univ : Set Y)) hP1A hP1_univ)

theorem P2_exists_compact_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ K, IsCompact K ∧ K ⊆ A := by
  intro _hP2
  exact ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _⟩

theorem P2_iff_P1_for_dense {X : Type*} [TopologicalSpace X] {A : Set X} (h : Dense A) : Topology.P2 A ↔ Topology.P1 A := by
  constructor
  · intro hP2
    exact P2_implies_P1 (A := A) hP2
  · intro hP1
    have hP3 : P3 A := P3_of_dense (A := A) h
    exact (P2_iff_P1_and_P3 (A := A)).mpr ⟨hP1, hP3⟩

theorem P2_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : Topology.P2 A := by
  exact P2_of_open (A := A) (isOpen_discrete _)

theorem P3_of_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} : closure A = Set.univ → Topology.P3 A := by
  intro hClosure
  intro x hxA
  have : x ∈ (Set.univ : Set X) := by
    simp
  simpa [hClosure, interior_univ] using this

theorem exists_open_P1_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ U : Set X, IsOpen U ∧ U ⊆ A ∧ Topology.P1 U := by
  intro _hP1A
  exact
    ⟨interior A, isOpen_interior, interior_subset,
      P1_interior (X := X) (A := A)⟩

theorem P3_closed_union_dense {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hB : Dense B) : Topology.P3 (A ∪ B) := by
  -- First, prove that the closure of `A ∪ B` is the whole space.
  have h_closure : closure (A ∪ B : Set X) = (Set.univ : Set X) := by
    -- Because `B` is dense, its closure is `univ`.
    have hB_closure : closure (B : Set X) = (Set.univ : Set X) := hB.closure_eq
    -- Since `B ⊆ A ∪ B`, we have `closure B ⊆ closure (A ∪ B)`.
    have h_subset : closure (B : Set X) ⊆ closure (A ∪ B) :=
      closure_mono (Set.subset_union_right : (B : Set X) ⊆ A ∪ B)
    -- Thus `univ ⊆ closure (A ∪ B)`.
    have h_univ_subset : (Set.univ : Set X) ⊆ closure (A ∪ B) := by
      simpa [hB_closure] using h_subset
    -- The reverse inclusion is trivial.
    apply Set.Subset.antisymm
    · intro x _; trivial
    · exact h_univ_subset
  -- Apply the lemma that a set whose closure is `univ` satisfies `P3`.
  exact (P3_of_closure_eq_univ (A := A ∪ B)) h_closure

theorem P1_sdiff_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : P1 (Aᶜ) := by
  have h_open : IsOpen (Aᶜ) := (isOpen_compl_iff).2 hA
  exact P1_of_open (A := Aᶜ) h_open

theorem exists_P3_subset_closed {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ C, IsClosed C ∧ C ⊆ A ∧ P3 C := by
  refine ⟨(∅ : Set X), isClosed_empty, Set.empty_subset _, ?_⟩
  exact P3_empty (X := X)

theorem P2_of_interior_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Dense (interior A) → P2 A := by
  intro hDense
  intro x hxA
  -- The closure of the interior is the whole space, hence its interior too.
  have hIntEq : interior (closure (interior A)) = (Set.univ : Set X) := by
    have hClosure : closure (interior A) = (Set.univ : Set X) := hDense.closure_eq
    simpa [hClosure, interior_univ]
  -- Conclude the desired membership.
  simpa [hIntEq]

theorem P1_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : P1 A := by
  exact P1_of_open (A := A) (isOpen_discrete _)

theorem P3_discrete {X : Type*} [TopologicalSpace X] [DiscreteTopology X] {A : Set X} : P3 A := by
  exact P3_of_open (A := A) (isOpen_discrete _)

theorem P1_and_P3_implies_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P3 A → Topology.P2 A := by
  intro hP1 hP3
  exact (P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩

theorem exists_open_between_P2_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ interior (closure A) ⊆ U := by
  intro hP2
  have hP3 : P3 A := P2_implies_P3 (A := A) hP2
  refine ⟨interior (closure A), isOpen_interior, ?_, subset_rfl⟩
  exact hP3

theorem P3_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P3 A → Topology.P3 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP3A
  simpa using
    (P3_prod (A := A) (B := (Set.univ : Set Y)) hP3A (P3_univ (X := Y)))

theorem P2_induction_on_closure {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ closure A, ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ A) → Topology.P2 A := by
  intro h x hxA
  -- `x` lies in the closure of `A`
  have hx_cl : (x : X) ∈ closure A := subset_closure hxA
  -- obtain an open neighbourhood of `x` contained in `A`
  rcases h x hx_cl with ⟨U, hU_open, hxU, hU_sub_A⟩
  -- this neighbourhood sits inside `interior A`
  have hU_sub_int : (U : Set X) ⊆ interior A :=
    interior_maximal hU_sub_A hU_open
  have hx_intA : x ∈ interior A := hU_sub_int hxU
  -- `interior A` is an open subset of `closure (interior A)`
  have hsubset : interior A ⊆ interior (closure (interior A)) := by
    apply interior_maximal
    · intro y hy
      exact subset_closure hy
    · exact isOpen_interior
  -- conclude
  exact hsubset hx_intA

theorem P2_prod_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} : Topology.P2 A → Topology.P2 (A ×ˢ (Set.univ : Set Y)) := by
  intro hP2A
  have hP2_univ : Topology.P2 (Set.univ : Set Y) := P2_univ (X := Y)
  simpa using (P2_prod (A := A) (B := (Set.univ : Set Y)) hP2A hP2_univ)

theorem P2_interiors_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P2 (interior A ∪ interior B) := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union isOpen_interior
  exact P2_of_open (A := interior A ∪ interior B) h_open

theorem exists_open_between_P1_P2 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P2 A → ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ U ⊆ interior (closure (interior A)) := by
  intro _ hP2
  exact
    ⟨interior (closure (interior A)), isOpen_interior, hP2, subset_rfl⟩

theorem P3_intersection_closed {X : Type*} [TopologicalSpace X] {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) : Topology.P3 A → Topology.P3 B → Topology.P3 (A ∩ B) := by
  intro hP3A hP3B
  -- First, translate `P3` into `P2` using the closedness of the sets.
  have hP2A : P2 A := (P3_iff_P2_for_closed (A := A) hA).1 hP3A
  have hP2B : P2 B := (P3_iff_P2_for_closed (A := B) hB).1 hP3B
  -- From closedness and `P2` we obtain `A = interior A` and `B = interior B`.
  have hEqA : (A : Set X) = interior A := P2_closed (A := A) hA hP2A
  have hEqB : (B : Set X) = interior B := P2_closed (A := B) hB hP2B
  -- Hence both `A` and `B` are open.
  have hA_open : IsOpen A := by
    simpa [hEqA.symm] using (isOpen_interior : IsOpen (interior A))
  have hB_open : IsOpen B := by
    simpa [hEqB.symm] using (isOpen_interior : IsOpen (interior B))
  -- The intersection of two open sets is open.
  have hAB_open : IsOpen (A ∩ B) := hA_open.inter hB_open
  -- Any open set satisfies `P3`.
  exact P3_of_open (A := A ∩ B) hAB_open

theorem P3_of_open_superset {X : Type*} [TopologicalSpace X] {A U : Set X} (hU : IsOpen U) (hAU : A ⊆ U) (hUcl : U ⊆ closure A) : Topology.P3 A := by
  intro x hxA
  have hxU : x ∈ U := hAU hxA
  have hUsub : (U : Set X) ⊆ interior (closure A) :=
    interior_maximal hUcl hU
  exact hUsub hxU

theorem exists_compact_P1_subset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ K, IsCompact K ∧ K ⊆ A ∧ Topology.P1 K := by
  refine ⟨(∅ : Set X), isCompact_empty, Set.empty_subset _, P1_empty (X := X)⟩

theorem P2_interior_closure_eq {X : Type*} [TopologicalSpace X] {A : Set X} (h : interior (closure A) = A) : Topology.P2 A := by
  -- First, observe that `A` is open because it is given as the interior of a set.
  have hA_open : IsOpen (A : Set X) := by
    have : IsOpen (interior (closure A)) := isOpen_interior
    simpa [h] using this
  -- Every open set satisfies `P2`.
  exact P2_of_open (A := A) hA_open

theorem P1_subset_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → ∃ B, B ⊆ A ∧ Topology.P3 B := by
  intro _hP1
  exact ⟨(∅ : Set X), Set.empty_subset _, P3_empty (X := X)⟩

theorem P2_of_forall_nhds {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ U, IsOpen U ∧ x ∈ U ∧ closure U ⊆ interior A) → Topology.P2 A := by
  intro h
  intro x hxA
  obtain ⟨U, hU_open, hxU, h_closure⟩ := h x hxA
  -- `U` is an open neighbourhood of `x` with `closure U ⊆ interior A`
  -- Hence `U ⊆ interior A`
  have hU_sub_int : (U : Set X) ⊆ interior A := by
    intro y hyU
    have hy_closure : (y : X) ∈ closure U := subset_closure hyU
    exact h_closure hy_closure
  -- Therefore `x ∈ interior A`
  have hx_intA : x ∈ interior A := hU_sub_int hxU
  -- `interior A ⊆ interior (closure (interior A))`
  have h_subset :
      interior A ⊆ interior (closure (interior A)) := by
    simpa [interior_interior] using
      (interior_mono
        (subset_closure : (interior A : Set X) ⊆ closure (interior A)))
  exact h_subset hx_intA

theorem P1_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P1 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; simpa using (P1_subsingleton (X := X) (A := A))

theorem P2_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P2 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; simpa using (P2_subsingleton (X := X) (A := A))

theorem P3_subsingleton_iff {X : Type*} [TopologicalSpace X] [Subsingleton X] {A : Set X} : Topology.P3 A ↔ True := by
  constructor
  · intro _; trivial
  · intro _; simpa using (P3_subsingleton (X := X) (A := A))

theorem P3_interior_closure_eq_univ {X : Type*} [TopologicalSpace X] {A : Set X} : interior (closure A) = Set.univ → Topology.P3 A := by
  intro h_eq
  intro x hxA
  have : (x : X) ∈ (Set.univ : Set X) := by
    simp
  simpa [h_eq] using this

theorem P1_unionᵢ {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, Topology.P1 (f i)) → Topology.P1 (⋃ i, interior (f i)) := by
  intro _hP1
  -- `P1` holds for every `interior (f i)` by `P1_interior`.
  have h : ∀ i, P1 (interior (f i)) := by
    intro i
    exact P1_interior (X := X) (A := f i)
  simpa using
    (P1_iUnion (X := X) (f := fun i => interior (f i)) h)

theorem P3_interiors_union {X : Type*} [TopologicalSpace X] (A B : Set X) : Topology.P3 (interior A ∪ interior B) := by
  have h_open : IsOpen (interior A ∪ interior B) :=
    (isOpen_interior : IsOpen (interior A)).union
      (isOpen_interior : IsOpen (interior B))
  exact P3_of_open (A := interior A ∪ interior B) h_open

theorem P2_of_closed_dense {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Dense A → Topology.P2 A := by
  intro hA_closed hA_dense
  -- First, deduce that `A` is the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    have h_closure : closure (A : Set X) = (Set.univ : Set X) :=
      hA_dense.closure_eq
    simpa [hA_closed.closure_eq] using h_closure
  -- Conclude using the fact that `P2` holds for `Set.univ`.
  simpa [hA_univ] using (P2_univ (X := X))

theorem P2_closed_complement {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → (Topology.P2 (Aᶜ) ↔ True) := by
  intro hA
  have hP2 : Topology.P2 (Aᶜ) := P2_complement_of_closed (A := A) hA
  constructor
  · intro _; trivial
  · intro _; exact hP2

theorem P3_iff_exists_open_closure_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A ↔ ∃ U : Set X, IsOpen U ∧ A ⊆ U ∧ closure U ⊆ closure A := by
  constructor
  · intro hP3
    refine ⟨interior (closure A), isOpen_interior, hP3, ?_⟩
    have h_subset : (interior (closure A) : Set X) ⊆ closure A :=
      interior_subset
    simpa [closure_closure] using (closure_mono h_subset)
  · rintro ⟨U, hU_open, hA_sub_U, h_closureU_sub_clA⟩
    intro x hxA
    have hxU : x ∈ U := hA_sub_U hxA
    -- `U ⊆ closure A`
    have hU_sub_clA : (U : Set X) ⊆ closure A := by
      intro y hyU
      have : (y : X) ∈ closure U := subset_closure hyU
      exact h_closureU_sub_clA this
    -- open set inside `closure A` lies in its interior
    have hU_sub_int : (U : Set X) ⊆ interior (closure A) :=
      interior_maximal hU_sub_clA hU_open
    exact hU_sub_int hxU

theorem exists_open_dense_P2_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ Dense U ∧ A ⊆ U ∧ Topology.P2 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, Set.subset_univ _, ?_⟩
  exact P2_univ (X := X)

theorem P2_Union_closed {X : Type*} [TopologicalSpace X] {ι : Sort*} {f : ι → Set X} (h_closed : ∀ i, IsClosed (f i)) : (∀ i, Topology.P2 (f i)) → Topology.P2 (⋃ i, f i) := by
  intro hP2
  exact P2_iUnion (X := X) (f := f) hP2

theorem P1_lebesgue_number {X : Type*} [TopologicalSpace X] (A : Set X) : Topology.P1 A → ∃ ε : ℝ, ε > 0 := by
  intro _
  exact ⟨1, by norm_num⟩

theorem P2_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → ∃ U, IsOpen U ∧ U ⊆ A ∧ Topology.P2 U := by
  intro _hP2A
  exact
    ⟨interior A, isOpen_interior, interior_subset,
      P2_interior (X := X) (A := A)⟩

theorem P1_iff_exists_closed_superset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ ∃ C, IsClosed C ∧ A ⊆ C ∧ C ⊆ closure (interior A) := by
  constructor
  · intro hP1
    exact ⟨closure (interior A), isClosed_closure, hP1, subset_rfl⟩
  · rintro ⟨C, _hC_closed, hA_sub_C, hC_sub_cl⟩
    exact Set.Subset.trans hA_sub_C hC_sub_cl

theorem P3_dense_open_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Dense A → (Topology.P3 A ↔ IsOpen (closure A)) := by
  intro hDense
  have hIsOpen : IsOpen (closure (A : Set X)) := by
    simpa [hDense.closure_eq] using isOpen_univ
  have hP3 : P3 A := P3_of_dense (X := X) (A := A) hDense
  exact ⟨fun _ => hIsOpen, fun _ => hP3⟩

theorem P2_prod_of_open {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : IsOpen A → Topology.P2 B → Topology.P2 (A ×ˢ B) := by
  intro hOpen hP2B
  exact P2_prod (A := A) (B := B) (P2_of_open (A := A) hOpen) hP2B

theorem P3_intersection_open {X : Type*} [TopologicalSpace X] {A U : Set X} (hU : IsOpen U) : Topology.P3 A → Topology.P3 (A ∩ U) := by
  intro hP3A
  intro x hx
  rcases hx with ⟨hxA, hxU⟩
  -- `P3` for `A`
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  -- The open set we shall work with
  have hW_open : IsOpen (interior (closure A) ∩ U) :=
    (isOpen_interior : IsOpen (interior (closure A))).inter hU
  have hxW : x ∈ (interior (closure A) ∩ U) := by
    exact ⟨hx_int, hxU⟩
  -- `W ⊆ closure (A ∩ U)`
  have hW_sub : (interior (closure A) ∩ U : Set X) ⊆ closure (A ∩ U) := by
    intro y hy
    have hy_int : y ∈ interior (closure A) := hy.1
    have hyU   : y ∈ U := hy.2
    have hy_clA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hy_int
    -- show that `y ∈ closure (A ∩ U)`
    have : y ∈ closure (A ∩ U) := by
      -- use the neighborhood characterization of closure
      apply (mem_closure_iff).2
      intro V hV_open hyV
      -- work in the open set `V ∩ U`
      have hVU_open : IsOpen (V ∩ U) := hV_open.inter hU
      have hy_VU : y ∈ V ∩ U := ⟨hyV, hyU⟩
      -- since `y ∈ closure A`, `A` meets `V ∩ U`
      have h_nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ U) hVU_open hy_VU
      rcases h_nonempty with ⟨z, ⟨hzVU, hzA⟩⟩
      rcases hzVU with ⟨hzV, hzU⟩
      -- `z` lies in `V ∩ (A ∩ U)`
      exact ⟨z, ⟨hzV, ⟨hzA, hzU⟩⟩⟩
    exact this
  -- an open subset of a closure lies in its interior
  have hW_sub_int :
      (interior (closure A) ∩ U : Set X) ⊆ interior (closure (A ∩ U)) :=
    interior_maximal hW_sub hW_open
  exact hW_sub_int hxW

theorem P1_of_closure_subset_interior_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : closure A ⊆ interior (closure (interior A)) → Topology.P1 A := by
  intro h
  intro x hxA
  have hx_closureA : (x : X) ∈ closure A := subset_closure hxA
  have hx_int : x ∈ interior (closure (interior A)) := h hx_closureA
  exact
    (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A)) hx_int

theorem P3_iff_exists_open_between {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A ↔ ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ A ⊆ U ∧ U ⊆ V ∧ V ⊆ closure A := by
  constructor
  · intro hP3
    rcases (P3_iff_exists_open_superset (X := X) (A := A)).1 hP3 with
      ⟨U, hU_open, hA_sub_U, hU_sub_cl⟩
    exact ⟨U, U, hU_open, hU_open, hA_sub_U, subset_rfl, hU_sub_cl⟩
  · rintro ⟨U, V, hU_open, hV_open, hA_sub_U, hU_sub_V, hV_sub_cl⟩
    have h_exists : ∃ W : Set X, IsOpen W ∧ A ⊆ W ∧ W ⊆ closure A :=
      ⟨V, hV_open, Set.Subset.trans hA_sub_U hU_sub_V, hV_sub_cl⟩
    exact (P3_iff_exists_open_superset (X := X) (A := A)).2 h_exists

theorem P2_closure_eq_interior_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P2 A → closure (interior (closure A)) = closure (interior A) := by
  intro hP2
  -- From `P2` we know the closures of `A` and `interior A` coincide.
  have hEq : closure (A : Set X) = closure (interior A) :=
    P2_implies_closure_eq (A := A) hP2
  -- Prove the desired equality by showing mutual inclusions.
  apply Set.Subset.antisymm
  · -- First inclusion:
    -- `interior (closure A)` is contained in `closure (interior A)`.
    have hsubset : interior (closure A) ⊆ closure (interior A) := by
      intro x hx
      have hx_cl : (x : X) ∈ closure A := interior_subset hx
      simpa [hEq] using hx_cl
    -- Taking closures preserves this inclusion.
    simpa [closure_closure] using (closure_mono hsubset)
  · -- Second inclusion:
    -- `interior A` is contained in `interior (closure A)`.
    have hsubset : interior A ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    -- Taking closures yields the required inclusion.
    exact closure_mono hsubset

theorem exists_maximal_P2_subset {X : Type*} [TopologicalSpace X] (A : Set X) : ∃ B, B ⊆ A ∧ Topology.P2 B ∧ (∀ C, C ⊆ A → Topology.P2 C → C ⊆ B) := by
  classical
  -- `S` is the collection of `P2` subsets of `A`.
  let S : Set (Set X) := {C | C ⊆ A ∧ P2 C}
  -- We take `B` to be the union of all sets in `S`.
  refine ⟨⋃₀ S, ?_, ?_, ?_⟩
  -- First, `B ⊆ A`.
  · intro x hx
    rcases Set.mem_sUnion.1 hx with ⟨C, hCS, hxC⟩
    exact (hCS.1) hxC
  -- Second, `B` satisfies `P2`.
  ·
    have hforall : ∀ C, C ∈ S → P2 C := by
      intro C hC
      exact hC.2
    have hP2B : P2 (⋃₀ S) := P2_sUnion (X := X) (S := S) hforall
    simpa using hP2B
  -- Finally, `B` is maximal among `P2` subsets of `A`.
  · intro C hC_sub hP2C
    intro x hxC
    have hC_in_S : C ∈ S := by
      show C ⊆ A ∧ P2 C
      exact ⟨hC_sub, hP2C⟩
    exact Set.mem_sUnion.2 ⟨C, hC_in_S, hxC⟩

theorem P3_iff_restrict_to_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} (hAB : A ⊆ B) (hDense : Dense A) : Topology.P3 B ↔ Topology.P3 A := by
  -- The closure of a dense set is the whole space.
  have hClA : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the closure of `B` is also the whole space, since `A ⊆ B`.
  have hClB : closure (B : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _; trivial
    ·
      have : (closure (A : Set X)) ⊆ closure B := closure_mono hAB
      simpa [hClA] using this
  -- From the two equalities we get the interiors of the closures.
  have hIntA : interior (closure A) = (Set.univ : Set X) := by
    simpa [hClA, interior_univ]
  have hIntB : interior (closure B) = (Set.univ : Set X) := by
    simpa [hClB, interior_univ]
  -- `P3` for `A` follows from density.
  have hP3A : P3 A := by
    intro x hxA
    have : (x : X) ∈ (Set.univ : Set X) := by trivial
    simpa [hIntA] using this
  -- `P3` for `B` is also immediate.
  have hP3B : P3 B := by
    intro x hxB
    have : (x : X) ∈ (Set.univ : Set X) := by trivial
    simpa [hIntB] using this
  -- Conclude the equivalence.
  exact ⟨fun _ => hP3A, fun _ => hP3B⟩

theorem exists_dense_open_P3_superset {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ Dense U ∧ A ⊆ U ∧ Topology.P3 U := by
  refine ⟨(Set.univ : Set X), isOpen_univ, dense_univ, Set.subset_univ _, ?_⟩
  exact P3_univ (X := X)

theorem P3_iinter {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P3 (interior A ∩ interior B) := by
  have h_open : IsOpen (interior A ∩ interior B) :=
    (isOpen_interior : IsOpen (interior A)).inter isOpen_interior
  exact P3_of_open (A := interior A ∩ interior B) h_open

theorem P1_closure {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Topology.P1 (closure A) := by
  intro hP1
  intro x hx_closureA
  -- First, `closure A ⊆ closure (interior A)` because `closure (interior A)` is a closed
  -- set containing `A`.
  have hsubset₁ : (closure A : Set X) ⊆ closure (interior A) := by
    have hclosed : IsClosed (closure (interior A)) := isClosed_closure
    exact closure_minimal hP1 hclosed
  -- Next, `closure (interior A) ⊆ closure (interior (closure A))` by monotonicity.
  have hsubset₂ :
      (closure (interior A) : Set X) ⊆ closure (interior (closure A)) := by
    have hInt_subset : interior A ⊆ interior (closure A) := by
      exact interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono hInt_subset
  -- Chain the two inclusions to obtain the result.
  exact hsubset₂ (hsubset₁ hx_closureA)

theorem P3_of_closure_is_open {X : Type*} [TopologicalSpace X] {A : Set X} (h : IsOpen (closure A)) : Topology.P3 A := by
  intro x hxA
  have hx_cl : (x : X) ∈ closure A := subset_closure hxA
  simpa [h.interior_eq] using hx_cl

theorem P2_closed_of_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Topology.P3 A → Topology.P2 A := by
  intro hA_closed hP3
  simpa using ((P3_iff_P2_for_closed (A := A) hA_closed).1 hP3)

theorem P3_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X} : A ⊆ B → Dense A → Topology.P3 B := by
  intro hAB hDense
  -- The closure of `A` is the whole space.
  have hClA : closure (A : Set X) = (Set.univ : Set X) := hDense.closure_eq
  -- Hence the closure of `B` is also the whole space.
  have hClB : closure (B : Set X) = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro x _
      simp
    ·
      have : closure (A : Set X) ⊆ closure B := closure_mono hAB
      simpa [hClA] using this
  -- Conclude using the lemma `P3_of_closure_eq_univ`.
  exact (P3_of_closure_eq_univ (A := B)) hClB

theorem P2_intersection_open {X : Type*} [TopologicalSpace X] {A U : Set X} : IsOpen U → Topology.P2 A → Topology.P2 (A ∩ U) := by
  intro hU_open hP2A
  intro x hxAU
  -- Split the hypothesis `x ∈ A ∩ U`
  have hxA : x ∈ A := hxAU.1
  have hxU : x ∈ U := hxAU.2
  -- Apply `P2` for `A`
  have hxIntCl : x ∈ interior (closure (interior A)) := hP2A hxA
  -- We will show that
  --   interior (closure (interior A)) ∩ U ⊆
  --   interior (closure (interior (A ∩ U))).
  -- This will give the result because `x` lies in the left–hand set.
  have h_subset :
      (interior (closure (interior A)) ∩ U : Set X) ⊆
        interior (closure (interior (A ∩ U))) := by
    -- The set on the left is open.
    have h_open :
        IsOpen (interior (closure (interior A)) ∩ U) :=
      (isOpen_interior).inter hU_open
    -- Show that it is contained in the closure on the right.
    have h_sub_closure :
        (interior (closure (interior A)) ∩ U : Set X) ⊆
          closure (interior (A ∩ U)) := by
      intro y hy
      -- `y` is in both components of the intersection
      have hyIntCl : y ∈ interior (closure (interior A)) := hy.1
      have hyU     : y ∈ U := hy.2
      -- Hence `y` is also in `closure (interior A)`.
      have hyCl : y ∈ closure (interior A) :=
        (interior_subset :
            interior (closure (interior A)) ⊆ closure (interior A)) hyIntCl
      -- Prove that `y` is in `closure (interior (A ∩ U))`
      have : y ∈ closure (interior (A ∩ U)) := by
        -- Use the neighbourhood criterion for closure.
        refine (mem_closure_iff).2 ?_
        intro V hV_open hyV
        -- Work inside the open set `V ∩ U`.
        have hVU_open : IsOpen (V ∩ U) := hV_open.inter hU_open
        have hyVU : y ∈ V ∩ U := ⟨hyV, hyU⟩
        -- Because `y ∈ closure (interior A)`, this set meets `interior A`.
        have h_nonempty :=
          ((mem_closure_iff).1 hyCl) (V ∩ U) hVU_open hyVU
        rcases h_nonempty with ⟨z, hzVU, hzIntA⟩
        -- Split the membership information for `z`.
        have hzV : z ∈ V := hzVU.1
        have hzU : z ∈ U := hzVU.2
        -- Show that `z ∈ interior (A ∩ U)`.
        have hzIntAU : z ∈ interior (A ∩ U) := by
          -- Consider the open set `interior A ∩ U` containing `z`.
          have hK_open : IsOpen (interior A ∩ U) :=
            (isOpen_interior).inter hU_open
          have hzK : z ∈ interior A ∩ U := ⟨hzIntA, hzU⟩
          have hK_sub : (interior A ∩ U : Set X) ⊆ A ∩ U := by
            intro w hw
            exact ⟨
              (interior_subset : interior A ⊆ A) hw.1,
              hw.2⟩
          have hK_int :=
            interior_maximal hK_sub hK_open
          exact hK_int hzK
        -- Produce the required witness for non-emptiness.
        exact ⟨z, ⟨hzV, hzIntAU⟩⟩
      exact this
    -- An open subset of a closure is contained in the corresponding interior.
    exact interior_maximal h_sub_closure h_open
  -- Apply the inclusion to `x`.
  have hx_mem :
      x ∈ (interior (closure (interior A)) ∩ U : Set X) :=
    ⟨hxIntCl, hxU⟩
  exact h_subset hx_mem

theorem P3_sUnion_interiors {X : Type*} [TopologicalSpace X] {S : Set (Set X)} : Topology.P3 (⋃₀ (Set.image interior S)) := by
  have hP3 : ∀ U ∈ Set.image interior S, Topology.P3 U := by
    intro U hU
    rcases hU with ⟨A, hAS, rfl⟩
    exact P3_interior (X := X) (A := A)
  simpa using (P3_unionₛ (X := X) (S := Set.image interior S) hP3)

theorem P3_product_swap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : Topology.P3 (A ×ˢ B) → Topology.P3 (B ×ˢ A) := by
  intro hP3
  simpa using
    (P3_image_homeomorph
        (e := Homeomorph.prodComm X Y)
        (A := (A ×ˢ B))) hP3

theorem exists_open_P3_subset_closure {X : Type*} [TopologicalSpace X] {A : Set X} : ∃ U, IsOpen U ∧ U ⊆ closure A ∧ Topology.P3 U := by
  refine ⟨interior (closure A), isOpen_interior, interior_subset, ?_⟩
  exact P3_of_open (A := interior (closure A)) isOpen_interior

theorem P2_nhds_basis {X : Type*} [TopologicalSpace X] {A : Set X} : (∀ x ∈ A, ∃ V ∈ 𝓝 x, V ⊆ interior A) → Topology.P2 A := by
  intro h
  intro x hxA
  -- obtain a neighbourhood `V` of `x` contained in `interior A`
  obtain ⟨V, hV_nhds, hV_subset⟩ := h x hxA
  -- refine to an open set `U` with `x ∈ U ⊆ V`
  rcases (mem_nhds_iff.1 hV_nhds) with ⟨U, hU_sub_V, hU_open, hxU⟩
  -- `U` is contained in `interior A`
  have hU_sub_intA : (U : Set X) ⊆ interior A :=
    Set.Subset.trans hU_sub_V hV_subset
  -- hence `U` is contained in `closure (interior A)`
  have hU_sub_cl : (U : Set X) ⊆ closure (interior A) :=
    Set.Subset.trans hU_sub_intA (subset_closure)
  -- an open subset of a closure lies in the corresponding interior
  have hU_sub_intCl : (U : Set X) ⊆ interior (closure (interior A)) :=
    interior_maximal hU_sub_cl hU_open
  -- conclude
  exact hU_sub_intCl hxU

theorem P1_prod_eq {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set (X × Y)} : Topology.P1 A ↔ Topology.P1 (Prod.swap ⁻¹' A) := by
  -- Define the homeomorphism that swaps the two factors.
  let e : (Y × X) ≃ₜ (X × Y) := Homeomorph.prodComm Y X
  -- Forward direction: pull back along `e`.
  have h₁ : Topology.P1 A → Topology.P1 (Prod.swap ⁻¹' A) := by
    intro hP1A
    simpa using
      (P1_preimage_homeomorph
          (X := Y × X) (Y := X × Y)
          (e := e) (B := A)) hP1A
  -- Backward direction: pull back along the inverse of `e`
  -- (whose underlying map is again `Prod.swap`).
  have h₂ : Topology.P1 (Prod.swap ⁻¹' A) → Topology.P1 A := by
    intro hP1swap
    simpa using
      (P1_preimage_homeomorph
          (X := X × Y) (Y := Y × X)
          (e := e.symm) (B := Prod.swap ⁻¹' A)) hP1swap
  exact ⟨h₁, h₂⟩

theorem P2_of_P1_and_dense {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A → Dense A → Topology.P2 A := by
  intro hP1 hDense
  have hP3 : Topology.P3 A := P3_of_dense (X := X) (A := A) hDense
  exact (P2_iff_P1_and_P3 (A := A)).2 ⟨hP1, hP3⟩

theorem P1_opensUnion {X : Type*} [TopologicalSpace X] {ι : Sort*} {U : ι → Set X} : (∀ i, IsOpen (U i)) → Topology.P1 (⋃ i, U i) := by
  intro hU
  have hP1_each : ∀ i, Topology.P1 (U i) := by
    intro i
    exact P1_of_open (A := U i) (hU i)
  simpa using (P1_iUnion (X := X) (f := U) hP1_each)

theorem P3_Union_open_sets {ι : Sort*} {X : Type*} [TopologicalSpace X] {U : ι → Set X} : (∀ i, IsOpen (U i)) → P3 (⋃ i, U i) := by
  intro hU_open
  have hP3_each : ∀ i, Topology.P3 (U i) := by
    intro i
    exact P3_of_open (A := U i) (hU_open i)
  simpa using (P3_iUnion (X := X) (f := U) hP3_each)

theorem P2_subset_exists_P3 {X : Type*} [TopologicalSpace X] {A : Set X} : P2 A → ∃ B, B ⊆ A ∧ P3 B := by
  intro hP2
  exact ⟨A, subset_rfl, P2_implies_P3 (A := A) hP2⟩

theorem P1_intersection_open_sets {X : Type*} [TopologicalSpace X] {A U : Set X} : IsOpen U → P1 A → P1 (A ∩ U) := by
  intro hU_open hP1A
  intro x hxAU
  -- Split the membership of `x`
  have hxA : x ∈ A := hxAU.1
  have hxU : x ∈ U := hxAU.2
  -- Use `P1` for `A`
  have hx_cl : x ∈ closure (interior A) := hP1A hxA
  -- Show that `x` belongs to `closure (interior (A ∩ U))`
  have : x ∈ closure (interior (A ∩ U)) := by
    -- Neighborhood characterization of closure for `interior A`
    have h_closure_prop := (mem_closure_iff).1 hx_cl
    -- Prove the analogous property for `interior (A ∩ U)`
    have h_prop :
        ∀ V, IsOpen V → x ∈ V → (V ∩ interior (A ∩ U)).Nonempty := by
      intro V hV_open hxV
      -- Work inside the open set `V ∩ U`
      have hVU_open : IsOpen (V ∩ U) := hV_open.inter hU_open
      have hxVU : x ∈ V ∩ U := ⟨hxV, hxU⟩
      -- From `x ∈ closure (interior A)` we get a point of `interior A`
      have h_nonempty : ((V ∩ U) ∩ interior A).Nonempty :=
        h_closure_prop (V ∩ U) hVU_open hxVU
      rcases h_nonempty with ⟨y, ⟨hyVU, hyIntA⟩⟩
      rcases hyVU with ⟨hyV, hyU⟩
      -- Show that `y ∈ interior (A ∩ U)`
      have h_subset :
          (interior A ∩ U : Set X) ⊆ interior (A ∩ U) := by
        -- `interior A ∩ U` is open and contained in `A ∩ U`
        have h_open_left : IsOpen (interior A ∩ U) :=
          (isOpen_interior).inter hU_open
        have h_left_sub : (interior A ∩ U : Set X) ⊆ A ∩ U := by
          intro z hz
          exact ⟨(interior_subset : interior A ⊆ A) hz.1, hz.2⟩
        exact interior_maximal h_left_sub h_open_left
      have hy_int : y ∈ interior (A ∩ U) := h_subset ⟨hyIntA, hyU⟩
      exact ⟨y, ⟨hyV, hy_int⟩⟩
    exact (mem_closure_iff).2 h_prop
  exact this

theorem P3_of_closed_dense_boundary {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → Dense (frontier A) → P3 A := by
  intro hA_closed hDense
  -- `frontier A ⊆ A` because `A` is closed (`closure A = A`).
  have h_frontier_sub_A : (frontier A : Set X) ⊆ A := by
    intro y hy
    -- `frontier A ⊆ closure A`
    have h_mem_closure : (y : X) ∈ closure A :=
      (frontier_subset_closure) hy
    simpa [hA_closed.closure_eq] using h_mem_closure
  -- Hence the closure of the frontier is contained in `A`.
  have h_closure_frontier_sub_A :
      closure (frontier A : Set X) ⊆ A :=
    closure_minimal h_frontier_sub_A hA_closed
  -- But the frontier is dense, so its closure is the whole space.
  have h_closure_frontier_univ :
      closure (frontier A : Set X) = (Set.univ : Set X) :=
    hDense.closure_eq
  -- Therefore `A` equals the whole space.
  have hA_univ : (A : Set X) = Set.univ := by
    apply Set.Subset.antisymm
    · exact Set.subset_univ _
    ·
      have : (Set.univ : Set X) ⊆ A := by
        simpa [h_closure_frontier_univ] using h_closure_frontier_sub_A
      exact this
  -- Consequently, `interior (closure A)` is the whole space.
  have h_int : interior (closure A) = (Set.univ : Set X) := by
    simpa [hA_closed.closure_eq, hA_univ, interior_univ]
  -- Establish `P3 A`.
  intro x hxA
  -- Rewrite the goal using the equalities obtained above.
  simpa [hA_closed.closure_eq, hA_univ, interior_univ] using hxA

theorem P2_unionᵢ_closed {ι : Sort*} {X : Type*} [TopologicalSpace X] {f : ι → Set X} : (∀ i, IsClosed (f i)) → (∀ i, Topology.P2 (f i)) → Topology.P2 (⋃ i, closure (f i)) := by
  intro hClosed hP2
  -- Each `closure (f i)` coincides with `f i` since `f i` is closed,
  -- hence it also satisfies `P2`.
  have hP2_closure : ∀ i, Topology.P2 (closure (f i)) := by
    intro i
    have h_eq : closure (f i) = f i := (hClosed i).closure_eq
    simpa [h_eq] using hP2 i
  -- Apply the `iUnion` lemma to the family `i ↦ closure (f i)`.
  simpa using
    (P2_iUnion (X := X) (f := fun i => closure (f i)) hP2_closure)

theorem P2_diff {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P2 A → IsClosed B → Topology.P2 (A \ B) := by
  intro hP2A hB_closed
  intro x hx
  -- Decompose the membership `x ∈ A \ B`
  have hxA   : x ∈ A := hx.1
  have hxNot : x ∉ B := hx.2
  -- From `P2` for `A`
  have hx_int : x ∈ interior (closure (interior A)) := hP2A hxA
  -- Two auxiliary open sets
  have hO₁ : IsOpen (interior (closure (interior A))) := isOpen_interior
  have hO₂ : IsOpen (Bᶜ : Set X) := (isOpen_compl_iff).2 hB_closed
  -- The open neighbourhood we will use
  let W : Set X := interior (closure (interior A)) ∩ Bᶜ
  have hW_open : IsOpen W := hO₁.inter hO₂
  have hxW : x ∈ W := by
    exact ⟨hx_int, hxNot⟩
  -- Show `W ⊆ closure (interior (A \ B))`
  have hW_sub : (W : Set X) ⊆ closure (interior (A \ B)) := by
    intro y hyW
    have hy_intCl : y ∈ interior (closure (interior A)) := hyW.1
    have hy_notB  : y ∈ Bᶜ := hyW.2
    have hy_cl    : y ∈ closure (interior A) :=
      (interior_subset :
        interior (closure (interior A)) ⊆ closure (interior A)) hy_intCl
    -- Use the neighbourhood criterion for closure
    have : y ∈ closure (interior (A \ B)) := by
      refine (mem_closure_iff).2 ?_
      intro V hV_open hyV
      -- Work inside `V ∩ Bᶜ`
      have hVB_open : IsOpen (V ∩ Bᶜ) := hV_open.inter hO₂
      have hy_VB : y ∈ V ∩ Bᶜ := ⟨hyV, hy_notB⟩
      -- `interior A` meets `V ∩ Bᶜ`
      have h_nonempty :=
        (mem_closure_iff).1 hy_cl (V ∩ Bᶜ) hVB_open hy_VB
      rcases h_nonempty with ⟨z, hz_VB, hz_intA⟩
      -- Split the information on `z`
      have hzV    : z ∈ V := hz_VB.1
      have hz_notB: z ∈ Bᶜ := hz_VB.2
      -- `z` lies in `interior (A \ B)`
      have hz_intDiff : z ∈ interior (A \ B) := by
        -- The open set `interior A ∩ Bᶜ`
        have h_open_aux : IsOpen (interior A ∩ Bᶜ) :=
          (isOpen_interior).inter hO₂
        have hz_aux_in : z ∈ interior A ∩ Bᶜ := ⟨hz_intA, hz_notB⟩
        have h_sub_aux :
            (interior A ∩ Bᶜ : Set X) ⊆ A \ B := by
          intro w hw
          exact ⟨(interior_subset : interior A ⊆ A) hw.1, hw.2⟩
        exact (interior_maximal h_sub_aux h_open_aux) hz_aux_in
      exact ⟨z, ⟨hzV, hz_intDiff⟩⟩
    exact this
  -- An open subset of a closure sits in the interior of that closure
  have hW_int :
      (W : Set X) ⊆ interior (closure (interior (A \ B))) :=
    interior_maximal hW_sub hW_open
  -- Finish
  exact hW_int hxW

theorem P1_nhds_iff {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 A ↔ (∀ x ∈ A, ∀ U ∈ 𝓝 x, (U ∩ interior A).Nonempty) := by
  classical
  constructor
  · intro hP1 x hxA U hU
    -- `x` lies in the closure of `interior A`
    have hx_cl : x ∈ closure (interior A) := hP1 hxA
    -- Choose an open neighbourhood `V` of `x` contained in `U`
    rcases mem_nhds_iff.1 hU with ⟨V, hV_sub, hV_open, hxV⟩
    -- `V` meets `interior A`
    have hV_int : (V ∩ interior A).Nonempty :=
      (mem_closure_iff).1 hx_cl V hV_open hxV
    -- Hence so does `U`
    rcases hV_int with ⟨y, hyV, hyIntA⟩
    exact ⟨y, ⟨hV_sub hyV, hyIntA⟩⟩
  · intro h x hxA
    -- Show that every open neighbourhood of `x` meets `interior A`
    have h_cl :
        ∀ V, IsOpen V → x ∈ V → (V ∩ interior A).Nonempty := by
      intro V hV_open hxV
      have hV_nhds : (V : Set X) ∈ 𝓝 x := hV_open.mem_nhds hxV
      exact h x hxA V hV_nhds
    -- Conclude `x ∈ closure (interior A)`
    exact (mem_closure_iff).2 h_cl

theorem P3_sdiff {X : Type*} [TopologicalSpace X] {A B : Set X} : Topology.P3 A → IsClosed B → Topology.P3 (A \ B) := by
  intro hP3A hB_closed
  intro x hx
  -- Decompose the hypothesis `x ∈ A \ B`.
  have hxA : x ∈ A := hx.1
  have hxNotB : x ∉ B := hx.2
  -- From `P3 A` we obtain `x ∈ interior (closure A)`.
  have hx_int : x ∈ interior (closure A) := hP3A hxA
  -- The complement of `B` is open.
  have h_open_Bc : IsOpen (Bᶜ : Set X) := (isOpen_compl_iff).2 hB_closed
  -- The open set we shall use.
  let U : Set X := interior (closure A) ∩ Bᶜ
  have hU_open : IsOpen U :=
    (isOpen_interior).inter h_open_Bc
  have hxU : x ∈ U := by
    dsimp [U]
    exact ⟨hx_int, by
      -- `x ∈ Bᶜ` is definitionally `x ∉ B`.
      simpa using hxNotB⟩
  -- Show that `U ⊆ closure (A \ B)`.
  have hU_sub : (U : Set X) ⊆ closure (A \ B) := by
    intro y hy
    rcases hy with ⟨hy_int, hy_notB⟩
    -- `y` lies in `closure A`.
    have hy_clA : y ∈ closure A :=
      (interior_subset : interior (closure A) ⊆ closure A) hy_int
    -- Prove `y ∈ closure (A \ B)` using the neighbourhood criterion.
    have : y ∈ closure (A \ B) := by
      apply (mem_closure_iff).2
      intro V hV_open hyV
      -- Work inside `V ∩ Bᶜ`.
      have hVB_open : IsOpen (V ∩ Bᶜ) := hV_open.inter h_open_Bc
      have hy_VB : y ∈ V ∩ Bᶜ := ⟨hyV, hy_notB⟩
      -- Since `y ∈ closure A`, `A` meets `V ∩ Bᶜ`.
      have h_nonempty :=
        (mem_closure_iff).1 hy_clA (V ∩ Bᶜ) hVB_open hy_VB
      rcases h_nonempty with ⟨z, hz_VB, hzA⟩
      -- `z` lies in `V ∩ (A \ B)`.
      have hz_mem : z ∈ V ∩ (A \ B) := by
        rcases hz_VB with ⟨hzV, hz_notB⟩
        exact ⟨hzV, ⟨hzA, hz_notB⟩⟩
      exact ⟨z, hz_mem⟩
    exact this
  -- An open subset of a closure lies in the corresponding interior.
  have hU_int : (U : Set X) ⊆ interior (closure (A \ B)) :=
    interior_maximal hU_sub hU_open
  -- Conclude: `x ∈ interior (closure (A \ B))`.
  exact hU_int hxU