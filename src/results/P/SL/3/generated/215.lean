

theorem nonempty_of_closure_interior_nonempty {X : Type*} [TopologicalSpace X]
    {A : Set X} :
    (closure (interior (A : Set X))).Nonempty → (A : Set X).Nonempty := by
  intro h_closure
  -- First, obtain non‐emptiness of `interior A` from that of its closure.
  have h_int : (interior (A : Set X)).Nonempty :=
    (closure_interior_nonempty_iff_interior_nonempty (A := A)).1 h_closure
  -- Any point of `interior A` is, a fortiori, a point of `A`.
  rcases h_int with ⟨x, hx_int⟩
  exact ⟨x, interior_subset hx_int⟩