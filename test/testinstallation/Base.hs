module Base where

fst3 :: (a,b,c) -> a
fst3 (x,y,z) = x
snd3 :: (a,b,c) -> b
snd3 (x,y,z) = y
thd3 :: (a,b,c) -> c
thd3 (x,y,z) = z

fst5 :: (a,b,c,d,e) -> a
fst5 (u,v,x,y,z) = u
snd5 :: (a,b,c,d,e) -> b
snd5 (u,v,x,y,z) = v
thd5 :: (a,b,c,d,e) -> c
thd5 (u,v,x,y,z) = x
frth5 :: (a,b,c,d,e) -> d
frth5 (u,v,x,y,z) = y
ffth5 :: (a,b,c,d,e) -> e
ffth5 (u,v,x,y,z) = z

               
