p _ (x:xs) (rij: rijen ) = 
   if eqString x rij 
      then rij
      else p xs : rijen

