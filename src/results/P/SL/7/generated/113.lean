

theorem Topology.P1_finite_iff_isOpen_of_T1
    {X : Type*} [TopologicalSpace X] [T1Space X] {F : Set X}
    (hF : F.Finite) :
    Topology.P1 F ↔ IsOpen F := by
  have hClosedF : IsClosed (F : Set X) := hF.isClosed
  constructor
  · intro hP1
    -- From `P1` and closedness obtain `closure (interior F) = F`.
    have hEq₁ : closure (interior F) = (F : Set X) :=
      (Topology.P1_closed_iff_closureInterior_eq (A := F) hClosedF).1 hP1
    -- `interior F` is finite, hence closed, so its closure is itself.
    have hClosedInt : IsClosed (interior F) := (hF.subset interior_subset).isClosed
    have hEq₂ : closure (interior F) = interior F := hClosedInt.closure_eq
    -- Combining the equalities gives `interior F = F`.
    have hIntEq : interior F = (F : Set X) := by
      calc
        interior F = closure (interior F) := by
          simpa [hEq₂]
        _ = F := hEq₁
    -- Therefore `F` is open.
    have : IsOpen (interior F) := isOpen_interior
    simpa [hIntEq] using this
  · intro hOpenF
    exact Topology.IsOpen_P1 (A := F) hOpenF