

theorem Topology.P1_compl_of_closed {X : Type*} [TopologicalSpace X] {A : Set X} (hA : IsClosed A) : Topology.P1 (Aᶜ) := by
  -- The complement of a closed set is open.
  have hOpen : IsOpen (Aᶜ) := by
    simpa [IsClosed] using hA
  -- Apply the lemma for open sets.
  exact P1_of_open (A := Aᶜ) hOpen

theorem Topology.P1_closure_interior {X : Type*} [TopologicalSpace X] {A : Set X} : Topology.P1 (closure (interior A)) := by
  intro x hx
  -- `interior A` is contained in `interior (closure (interior A))`
  have hsubset : (interior A : Set X) ⊆ interior (closure (interior A)) := by
    -- apply monotonicity of `interior` to the inclusion `interior A ⊆ closure (interior A)`
    have h : interior (interior A) ⊆ interior (closure (interior A)) :=
      interior_mono (subset_closure : (interior A : Set X) ⊆ closure (interior A))
    simpa [interior_interior] using h
  -- taking closures gives the desired inclusion of closures
  have hclosure :
      closure (interior A) ⊆ closure (interior (closure (interior A))) :=
    closure_mono hsubset
  exact hclosure hx