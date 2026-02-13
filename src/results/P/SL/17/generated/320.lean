

theorem Topology.dense_of_dense_subset {X : Type*} [TopologicalSpace X] {A B : Set X}
    (hAB : A ⊆ B) (hDenseA : Dense A) : Dense B := by
  -- The closure of a dense set is the whole space.
  have hClosureA : closure A = (Set.univ : Set X) := hDenseA.closure_eq
  -- Monotonicity of `closure` under the inclusion `A ⊆ B`.
  have hSubset : closure A ⊆ closure B := closure_mono hAB
  -- Hence `closure B` contains `univ`.
  have hUnivSubset : (Set.univ : Set X) ⊆ closure B := by
    simpa [hClosureA] using hSubset
  -- Now we have the desired equality `closure B = univ`.
  have hClosureB : closure B = (Set.univ : Set X) := by
    apply Set.Subset.antisymm
    · intro _x _hx; simp
    · exact hUnivSubset
  -- Translate the closure equality into the `Dense` property.
  simpa using (Topology.dense_iff_closure_eq_univ (A := B)).2 hClosureB