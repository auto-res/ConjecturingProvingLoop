

theorem P3_iff_exists_open_subset {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P3 A ↔ ∃ U, IsOpen U ∧ U ⊆ closure A ∧ A ⊆ interior U := by
  -- First direction : `P3 A → ∃ U, ...`
  constructor
  · intro hP3
    -- Choose `U = interior (closure A)`
    refine
      ⟨interior (closure A), isOpen_interior, interior_subset, ?_⟩
    -- Since `U` is open, its interior is itself, hence
    -- `A ⊆ interior U` follows from `P3`.
    have h_eq : interior (interior (closure A)) = interior (closure A) := by
      simpa using interior_interior (closure A)
    simpa [h_eq] using hP3
  -- Second direction : the existence of an open `U` implies `P3 A`.
  · rintro ⟨U, hUopen, hU_subset, hA_subset⟩
    dsimp [Topology.P3] at *
    intro x hxA
    -- `x` belongs to `interior U`.
    have hx_intU : x ∈ interior U := hA_subset hxA
    -- Monotonicity of `interior` with `U ⊆ closure A`.
    have h_intU_to_intClA :
        (interior U : Set X) ⊆ interior (closure A) :=
      interior_mono hU_subset
    exact h_intU_to_intClA hx_intU