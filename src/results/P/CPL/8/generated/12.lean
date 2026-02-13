

theorem P1_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P1 A → P1 B → P1 (Set.prod A B) := by
  intro hP1A hP1B
  intro p hpProd
  rcases hpProd with ⟨hpA, hpB⟩
  -- Coordinates lie in the respective closures of the interiors
  have hx_cl : p.1 ∈ closure (interior A) := hP1A hpA
  have hy_cl : p.2 ∈ closure (interior B) := hP1B hpB
  -- Hence the point lies in the product of these closures
  have hp_prod_cl : p ∈ Set.prod (closure (interior A)) (closure (interior B)) :=
    ⟨hx_cl, hy_cl⟩
  -- Identify this product with the closure of the product of the interiors
  have h_cl_eq :
      closure (Set.prod (interior A) (interior B)) =
        Set.prod (closure (interior A)) (closure (interior B)) := by
    simpa using closure_prod_eq (s := interior A) (t := interior B)
  have hp_in_cl : p ∈ closure (Set.prod (interior A) (interior B)) := by
    simpa [h_cl_eq] using hp_prod_cl
  -- The closure we have is contained in the desired closure
  have h_subset :
      closure (Set.prod (interior A) (interior B)) ⊆
        closure (interior (Set.prod A B)) := by
    -- First show the underlying sets are related
    have h_sub :
        Set.prod (interior A) (interior B) ⊆ interior (Set.prod A B) := by
      have h_open : IsOpen (Set.prod (interior A) (interior B)) :=
        (isOpen_interior.prod isOpen_interior)
      have h_sub' :
          Set.prod (interior A) (interior B) ⊆ Set.prod A B := by
        intro q hq
        rcases hq with ⟨hqa, hqb⟩
        exact ⟨interior_subset hqa, interior_subset hqb⟩
      exact interior_maximal h_sub' h_open
    exact closure_mono h_sub
  exact h_subset hp_in_cl

theorem P3_prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {A : Set X} {B : Set Y} : P3 A → P3 B → P3 (Set.prod A B) := by
  intro hP3A hP3B
  intro p hpProd
  rcases hpProd with ⟨hpA, hpB⟩
  -- coordinates live in the relevant interiors of closures
  have hSA_mem : p.1 ∈ interior (closure A) := hP3A hpA
  have hSB_mem : p.2 ∈ interior (closure B) := hP3B hpB
  -- auxiliary open sets
  set SA := interior (closure A) with hSAdef
  set SB := interior (closure B) with hSBdef
  -- open neighbourhood around `p`
  let O : Set (X × Y) := Set.prod SA SB
  have hOopen : IsOpen O := by
    have hSAopen : IsOpen SA := by
      have : IsOpen (interior (closure A)) := isOpen_interior
      simpa [hSAdef] using this
    have hSBopen : IsOpen SB := by
      have : IsOpen (interior (closure B)) := isOpen_interior
      simpa [hSBdef] using this
    simpa [O] using hSAopen.prod hSBopen
  have hpO : p ∈ O := by
    dsimp [O]
    have hpSA : p.1 ∈ SA := by
      simpa [hSAdef] using hSA_mem
    have hpSB : p.2 ∈ SB := by
      simpa [hSBdef] using hSB_mem
    exact ⟨hpSA, hpSB⟩
  -- `O` is contained in the interior of the desired closure
  have hO_sub : O ⊆ interior (closure (Set.prod A B)) := by
    -- first show `O ⊆ closure (A × B)`
    have hO_sub_cl : O ⊆ closure (Set.prod A B) := by
      intro q hqO
      dsimp [O] at hqO
      rcases hqO with ⟨hqSA, hqSB⟩
      -- coordinates lie in the respective closures
      have hq_clA : q.1 ∈ closure A := by
        have : q.1 ∈ interior (closure A) := by
          simpa [hSAdef] using hqSA
        exact interior_subset this
      have hq_clB : q.2 ∈ closure B := by
        have : q.2 ∈ interior (closure B) := by
          simpa [hSBdef] using hqSB
        exact interior_subset this
      have hq_prod : q ∈ Set.prod (closure A) (closure B) := ⟨hq_clA, hq_clB⟩
      have h_closure_prod_eq : closure (Set.prod A B) = Set.prod (closure A) (closure B) := by
        simpa using closure_prod_eq (s := A) (t := B)
      simpa [h_closure_prod_eq] using hq_prod
    -- use `interior_maximal`
    exact interior_maximal hO_sub_cl hOopen
  -- conclude the desired membership
  have hp_int : p ∈ interior (closure (Set.prod A B)) := hO_sub hpO
  simpa using hp_int