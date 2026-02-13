

theorem Topology.closure_interior_closure_inter_subset
    {X : Type*} [TopologicalSpace X] {A B : Set X} :
    closure (interior (closure (A ∩ B))) ⊆
      closure (interior (closure A)) ∩ closure (interior (closure B)) := by
  intro x hx
  -- auxiliary inclusions for the factor `A`
  have hAB_to_A : (A ∩ B : Set X) ⊆ A := by
    intro z hz; exact hz.1
  have hClosureAB_to_ClosureA : closure (A ∩ B) ⊆ closure A :=
    closure_mono hAB_to_A
  have hIntMonoA :
      interior (closure (A ∩ B)) ⊆ interior (closure A) :=
    interior_mono hClosureAB_to_ClosureA
  have hClosMonoA :
      closure (interior (closure (A ∩ B))) ⊆
        closure (interior (closure A)) :=
    closure_mono hIntMonoA
  -- auxiliary inclusions for the factor `B`
  have hAB_to_B : (A ∩ B : Set X) ⊆ B := by
    intro z hz; exact hz.2
  have hClosureAB_to_ClosureB : closure (A ∩ B) ⊆ closure B :=
    closure_mono hAB_to_B
  have hIntMonoB :
      interior (closure (A ∩ B)) ⊆ interior (closure B) :=
    interior_mono hClosureAB_to_ClosureB
  have hClosMonoB :
      closure (interior (closure (A ∩ B))) ⊆
        closure (interior (closure B)) :=
    closure_mono hIntMonoB
  exact And.intro (hClosMonoA hx) (hClosMonoB hx)