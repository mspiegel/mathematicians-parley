$( proofs/setmm/subset-by-double-difference/subset-by-double-difference, elaborated from proofs/setmm/subset-by-double-difference.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/sets/subset-antisymmetric.mm $]

${
  $d k m $.
  $d A k m $.
  $d B k m $.
  proofs.setmm.subset-by-double-difference.subset-by-double-difference $p |- ( ( A e. _V /\ B e. _V ) -> ( A C_ B <-> ( B \ ( B \ A ) ) = A ) ) $=
    ( cvv wcel wa wss cdif wceq simpl simpr syl difexg id jca vm cv wral wn wb eldif a1i mpbid mpbird simprd pm2.21dd ex pm2.18d ralrimiva dfss3 vk ssel2 pm2.01d stdlib.sets.subset-antisymmetric difss sseq1d impbida ) ACDZBCDZEZABFZBBAGZGZAHZUSUTEZVBCDZUQEZVBAFZEZAVBFZEVCVDVHVIVDVFVGVDVEUQVDURVEVDUSURUSUTIZUQURJKBVACLKVDUSUQVJUSUQUQUQURIUQMKKNVDVGOPZADZOVBQZVDVLOVBVDVKVBDZEZVLVOVLRZVLVOVPEZVKVADZVLVQVRVKBDZVPEZVQVSVPVQVSVRRZEZVSVQVOWBVOVPIZVOVNWBVDVNJZVNWBSZVOVKBVATZUAZUBZKZVSWAIKVOVPJNVRVTSVQVKBATUAUCVQVSWAWIUDUEUFUGUHVGVMSVDOVBAUIUAUCNVDVIUJPZVBDZUJAQZVDWKUJAVDWJADZEZWKWJBDZWJVADZRZEZWNWOWQWNUTWMEWOWNUTWMWNVDUTVDWMIUSUTJKVDWMJZNABWJUKKWNWPWNWPWQWNWPEZWMWQWTWNWMWNWPIWSKWTWOWMRZWTWPWOXAEZWNWPJWPXBSWTWJBATUAUBUDUEUFULNWKWRSWNWJBVATUAUCUHVIWLSVDUJAVBUIUAUCNVBAUMKUSVCEZVBBFZUTXDXCBVAUNUAXCVBABUSVCJUOUBUP $.
$}
