module MiosSpec (spec) where

import System.IO.Unsafe
import Test.Hspec
import SAT.Mios

testRun :: Spec
testRun = do
  describe "SAT problems" $ do
    let res = unsafePerformIO $ solveSAT (CNFDescription 4 5 Nothing) [[1,2,-3], [-1, -4], [2,4], [1,-3,4], [-3,4]]
    it "a simple SAT" $ res `shouldBe` [-1,2,-3,-4]

spec :: Spec
spec = testRun
