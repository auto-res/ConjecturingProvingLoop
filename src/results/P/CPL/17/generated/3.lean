

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