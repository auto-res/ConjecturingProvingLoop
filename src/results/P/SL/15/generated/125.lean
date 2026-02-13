

theorem P1_prod_right {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [Nonempty X]
    {B : Set Y} :
    Topology.P1 ((Set.univ : Set X) ×ˢ B) → Topology.P1 B := by
  intro hProd
  dsimp [Topology.P1] at hProd
  dsimp [Topology.P1]
  intro y hyB
  classical
  have x : X := Classical.arbitrary X
  have h_mem_prod : ((x, y) : X × Y) ∈ ((Set.univ : Set X) ×ˢ B) := by
    exact And.intro (by trivial) hyB
  have h_closure_mem :
      ((x, y) : X × Y) ∈ closure (interior ((Set.univ : Set X) ×ˢ B)) :=
    hProd h_mem_prod
  have h_int_prod :
      interior ((Set.univ : Set X) ×ˢ B) =
        (Set.univ : Set X) ×ˢ interior B := by
    simpa [interior_univ] using
      interior_prod_eq (s := (Set.univ : Set X)) (t := B)
  have h_closure_prod :
      closure (interior ((Set.univ : Set X) ×ˢ B)) =
        (Set.univ : Set X) ×ˢ closure (interior B) := by
    calc
      closure (interior ((Set.univ : Set X) ×ˢ B))
          = closure ((Set.univ : Set X) ×ˢ interior B) := by
            simpa [h_int_prod]
      _ = closure (Set.univ : Set X) ×ˢ closure (interior B) := by
            simpa [closure_univ] using
              closure_prod_eq (s := (Set.univ : Set X)) (t := interior B)
      _ = (Set.univ : Set X) ×ˢ closure (interior B) := by
            simpa [closure_univ]
  have h_mem_prod_closure :
      ((x, y) : X × Y) ∈ (Set.univ : Set X) ×ˢ closure (interior B) := by
    simpa [h_closure_prod] using h_closure_mem
  exact (Set.mem_prod.1 h_mem_prod_closure).2