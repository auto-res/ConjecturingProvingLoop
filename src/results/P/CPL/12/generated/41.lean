

theorem P2_inter {X : Type*} [TopologicalSpace X] {A B : Set X} : P2 A → P2 B → P2 (A ∩ B) := by
  --  First, unpack the two `P2` hypotheses.
  intro hA hB
  intro x hx
  rcases hx with ⟨hxA, hxB⟩
  --  Points furnished by the two inclusions.
  have hxA' : x ∈ interior (closure (interior (A : Set X))) := hA hxA
  have hxB' : x ∈ interior (closure (interior (B : Set X))) := hB hxB
  ----------------------------------------------------------------
  --  Define an auxiliary open neighbourhood of `x`.
  ----------------------------------------------------------------
  let O : Set X :=
    interior (closure (interior (A : Set X))) ∩
      interior (closure (interior (B : Set X)))
  have hOopen : IsOpen O :=
    (isOpen_interior.inter isOpen_interior)
  have hxO : (x : X) ∈ O := by
    dsimp [O] at *
    exact And.intro hxA' hxB'
  ----------------------------------------------------------------
  --  Key inclusion: `O ⊆ closure (interior (A ∩ B))`.
  ----------------------------------------------------------------
  have hOsub :
      (O : Set X) ⊆ closure (interior ((A ∩ B : Set X))) := by
    intro y hy
    rcases hy with ⟨hyA', hyB'⟩
    --  `y` is in the two closures of the interiors.
    have hyA_cl : y ∈ closure (interior (A : Set X)) :=
      interior_subset hyA'
    have hyB_cl : y ∈ closure (interior (B : Set X)) :=
      interior_subset hyB'
    --  We show directly that `y ∈ closure (interior (A ∩ B))`.
    have : y ∈ closure (interior ((A ∩ B : Set X))) := by
      --  Use the neighbourhood characterisation of the closure.
      apply (mem_closure_iff).2
      intro U hUopen hyU
      ----------------------------------------------------------------
      --  Build a smaller open set `W` lying inside the two big closures.
      ----------------------------------------------------------------
      let W : Set X :=
        U ∩ interior (closure (interior (A : Set X))) ∩
          interior (closure (interior (B : Set X)))
      have hWopen : IsOpen W := by
        have h₁ : IsOpen (U ∩ interior (closure (interior (A : Set X)))) :=
          hUopen.inter isOpen_interior
        simpa [W] using h₁.inter isOpen_interior
      have hyW : (y : X) ∈ W := by
        dsimp [W] at *
        exact ⟨⟨hyU, hyA'⟩, hyB'⟩
      ----------------------------------------------------------------
      --  `W` meets `interior A`.
      ----------------------------------------------------------------
      have hnonA : (W ∩ interior (A : Set X)).Nonempty := by
        have h := (mem_closure_iff).1 hyA_cl
        have h' := h W hWopen hyW
        --  Re‐arrange the intersection to the desired shape.
        simpa [W, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using h'
      rcases hnonA with ⟨a, haW, haIntA⟩
      ----------------------------------------------------------------
      --  Shrink once more inside `interior A`.
      ----------------------------------------------------------------
      let V : Set X := interior (A : Set X) ∩ W
      have hVopen : IsOpen V := isOpen_interior.inter hWopen
      have haV : (a : X) ∈ V := by
        dsimp [V] at *
        exact ⟨haIntA, haW⟩
      --  `a ∈ closure (interior B)` (since `a ∈ W`).
      have ha_clB : a ∈ closure (interior (B : Set X)) := by
        have : (a : X) ∈ interior (closure (interior (B : Set X))) := by
          --  Extract the relevant component of `a ∈ W`.
          have hAW : a ∈ W := haW
          dsimp [W] at hAW
          exact hAW.2
        exact interior_subset this
      ----------------------------------------------------------------
      --  Hence `V` meets `interior B`.
      ----------------------------------------------------------------
      have hnonB : (V ∩ interior (B : Set X)).Nonempty := by
        have h := (mem_closure_iff).1 ha_clB
        have h' := h V hVopen haV
        simpa [V, Set.inter_comm, Set.inter_left_comm, Set.inter_assoc] using h'
      rcases hnonB with ⟨z, hzV, hzIntB⟩
      --  Summarise the information on `z`.
      have hzIntA : z ∈ interior (A : Set X) := hzV.1
      have hzW   : z ∈ W := hzV.2
      have hzU   : (z : X) ∈ U := by
        dsimp [W] at hzW
        exact hzW.1.1
      --  `z` lies in the interior of `A ∩ B`.
      have hzIntAB : (z : X) ∈ interior ((A ∩ B : Set X)) := by
        --  `interior (A ∩ B) = interior A ∩ interior B`
        have : z ∈ interior (A : Set X) ∩ interior (B : Set X) :=
          ⟨hzIntA, hzIntB⟩
        simpa [interior_inter] using this
      --  Produce the required intersection point.
      exact ⟨z, hzU, hzIntAB⟩
    exact this
  ----------------------------------------------------------------
  --  Apply `interior_maximal` to obtain the desired membership.
  ----------------------------------------------------------------
  have hfinal :
      x ∈ interior (closure (interior ((A ∩ B : Set X)))) :=
    (interior_maximal hOsub hOopen) hxO
  simpa using hfinal