module Ex12 where

fail3 p []    = p +# p
fail3 p (h:t) = if p True then [h] else t

(+#) :: Int -> Int -> Int
(+#) = (+)
