

theorem Topology.P3_iff_forall_open_nbhd_closure {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P3 A ↔
      ∀ x : X, x ∈ (A : Set X) →
        ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ closure (A : Set X) := by
  constructor
  · intro hP3 x hxA
    -- Choose the canonical open neighbourhood `interior (closure A)`.
    have hx_int : x ∈ interior (closure (A : Set X)) := hP3 hxA
    exact
      ⟨interior (closure (A : Set X)), isOpen_interior, hx_int, interior_subset⟩
  · intro h
    intro x hxA
    -- Extract an open neighbourhood of `x` contained in `closure A`.
    rcases h x hxA with ⟨U, hOpenU, hxU, hU_sub⟩
    -- This witnesses that `x` is in the interior of `closure A`.
    have : (∃ V : Set X, V ⊆ closure (A : Set X) ∧ IsOpen V ∧ x ∈ V) :=
      ⟨U, hU_sub, hOpenU, hxU⟩
    simpa [mem_interior] using this