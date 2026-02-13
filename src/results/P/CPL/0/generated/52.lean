

theorem isOpen_of_P2_closed {X : Type*} [TopologicalSpace X] {A : Set X} : IsClosed A → P2 A → IsOpen A := by
  intro hClosed hP2
  -- `P2 A` gives `A ⊆ interior (closure (interior A))`.
  have h1 : (A : Set X) ⊆ interior (closure (interior A)) := hP2
  -- Since `A` is closed, `closure (interior A) ⊆ A`.
  have h2 : closure (interior (A : Set X)) ⊆ A := by
    have h : closure (interior (A : Set X)) ⊆ closure (A : Set X) :=
      closure_mono (interior_subset : (interior A : Set X) ⊆ A)
    simpa [hClosed.closure_eq] using h
  -- Hence `interior (closure (interior A)) ⊆ interior A`.
  have h3 :
      interior (closure (interior (A : Set X))) ⊆ interior A :=
    interior_mono h2
  -- Combine inclusions to get `A ⊆ interior A`.
  have h4 : (A : Set X) ⊆ interior A := fun x hx => h3 (h1 hx)
  -- Together with `interior_subset`, this yields equality.
  have h_eq : interior A = A := Set.Subset.antisymm interior_subset h4
  -- Conclude that `A` is open.
  have : IsOpen (interior (A : Set X)) := isOpen_interior
  simpa [h_eq] using this

theorem P1_empty_iff_true {X : Type*} [TopologicalSpace X] : P1 (∅ : Set X) ↔ True := by
  constructor
  · intro _
    trivial
  · intro _
    exact P1_empty