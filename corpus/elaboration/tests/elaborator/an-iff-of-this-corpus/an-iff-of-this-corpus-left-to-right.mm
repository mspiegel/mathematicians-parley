$( tests/elaborator/an-iff-of-this-corpus/an-iff-of-this-corpus-left-to-right, elaborated from tests/elaborator/an-iff-of-this-corpus.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ tests/elaborator/an-iff-of-this-corpus/zero-divides-restated.mm $]

${
  tests.elaborator.an-iff-of-this-corpus.an-iff-of-this-corpus-left-to-right $p |- ( ( A e. ZZ /\ 0 || A ) -> A = 0 ) $=
    ( cz wcel cc0 cdvds wbr wa wceq simpr wb simpl id syl tests.elaborator.an-iff-of-this-corpus.zero-divides-restated mpbid ) ABCZDAEFZGZQADHZPQIRPQSJRPPPQKPLMANMO $.
$}
