

theorem P1_dense_iff_denseInterior {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → (Dense A ↔ Dense (interior A)) := by
  intro hP1
  -- From `P1`, the two closures coincide.
  have h_cl_eq : closure A = closure (interior A) :=
    (Topology.P1_iff_closure_eq_closure_interior (X := X) (A := A)).1 hP1
  -- Characterisations of density via closures.
  have hDenseA : Dense A ↔ closure A = (Set.univ : Set X) :=
    (dense_iff_closure_eq (s := A))
  have hDenseInt : Dense (interior A) ↔
      closure (interior A) = (Set.univ : Set X) :=
    (dense_iff_closure_eq (s := interior A))
  -- Use the common closure to relate the two densities.
  constructor
  · intro hDA
    have hClA : closure A = (Set.univ : Set X) := hDenseA.mp hDA
    have hClInt : closure (interior A) = (Set.univ : Set X) := by
      simpa [h_cl_eq] using hClA
    exact hDenseInt.mpr hClInt
  · intro hDInt
    have hClInt : closure (interior A) = (Set.univ : Set X) :=
      hDenseInt.mp hDInt
    have hClA : closure A = (Set.univ : Set X) := by
      simpa [h_cl_eq] using hClInt
    exact hDenseA.mpr hClA