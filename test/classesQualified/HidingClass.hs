module HidingClass where

import ClassA hiding (A)

instance A Int where
  id2 = id
