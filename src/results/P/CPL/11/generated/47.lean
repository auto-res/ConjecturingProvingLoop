

theorem P1_of_P3_and_closed {X : Type*} [TopologicalSpace X] {A : Set X} (h3 : P3 A) (h_closed : IsClosed A) : P1 A := by
  intro x hxA
  -- `x` is in the interior of the closure of `A`.
  have hxIntClosure : x ∈ interior (closure (A : Set X)) := h3 hxA
  -- Since `A` is closed, its closure is itself.
  have h_closure_eq : (closure (A : Set X)) = A := h_closed.closure_eq
  -- Hence `x` is in `interior A`.
  have hxInt : x ∈ interior (A : Set X) := by
    simpa [h_closure_eq] using hxIntClosure
  -- The interior of `A` is contained in `closure (interior A)`.
  exact (subset_closure : (interior A : Set X) ⊆ closure (interior A)) hxInt

theorem P1_iff_P2_of_open {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsOpen A) : P1 A ↔ P2 A := by
  exact ⟨fun _ => P2_of_open (A := A) hA,
         fun _ => P1_of_open (A := A) hA⟩

theorem P2_prod_snd_univ {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} (hA : P2 A) : P2 ((interior (Set.univ : Set X)) ×ˢ A) := by
  simpa [interior_univ] using
    (P2_prod_right (X := X) (Y := X) (B := A) hA)