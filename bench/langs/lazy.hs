{-# LANGUAGE BangPatterns #-}
import System.CPUTime
import Text.Printf
-- a hand-built lazy stream, as a Clojure lazy-seq is: a cell per element
data Stream = Cons !Int Stream | Nil
from :: Int -> Stream
from n = Cons n (from (n + 1))
takeS :: Int -> Stream -> Stream
takeS 0 _ = Nil
takeS n (Cons x r) = Cons x (takeS (n - 1) r)
takeS _ Nil = Nil
sumS :: Stream -> Int
sumS = go 0 where go !a Nil = a
                  go !a (Cons x r) = go (a + x) r
timeIt :: String -> Int -> IO ()
timeIt label v = do
  t0 <- getCPUTime
  let r = v
  r `seq` return ()
  t1 <- getCPUTime
  printf "%-44s %8.1f ms  (%d)\n" label (fromIntegral (t1 - t0) / 1e9 :: Double) r
main :: IO ()
main = do
  n <- return (1000000 :: Int)
  timeIt "sum (take n [0..])  (lists)" (sum (take n [0..]))
  timeIt "sumS (takeS n (from 0))  (hand stream)" (sumS (takeS n (from 0)))
