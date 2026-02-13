

theorem Topology.closure_has_P1_of_P1 {X : Type*} [TopologicalSpace X] {A : Set X} :
    Topology.P1 A → Topology.P1 (closure A) := by
  intro hA
  dsimp [Topology.P1] at hA ⊢
  -- First, take closures of both sides of `hA`.
  have h1 : (closure A : Set X) ⊆ closure (interior A) := by
    have : (closure A : Set X) ⊆ closure (closure (interior A)) :=
      closure_mono hA
    simpa using this
  -- Next, use the monotonicity of `interior` and `closure` to enlarge the right-hand side.
  have h2 : closure (interior A) ⊆ closure (interior (closure A)) := by
    have : (interior A : Set X) ⊆ interior (closure A) :=
      interior_mono (subset_closure : (A : Set X) ⊆ closure A)
    exact closure_mono this
  -- Combining the two inclusions yields the desired result.
  exact Set.Subset.trans h1 h2