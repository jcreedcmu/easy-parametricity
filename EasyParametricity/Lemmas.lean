omit [Limits.HasLimits C] in 
theorem one_limit_iso {J : Type} [Category J]  (F : J ⥤ C) [Limits.HasLimit F]
         (A : Limits.LimitCone F) : Limits.limit F = A.cone.pt := 
  by
   apply Univalent.univalence
   exact (Limits.limit.isoLimitCone A)
