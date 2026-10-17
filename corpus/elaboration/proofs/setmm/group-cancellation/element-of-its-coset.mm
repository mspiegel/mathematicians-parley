$( proofs/setmm/group-cancellation/element-of-its-coset, elaborated from proofs/setmm/group-cancellation.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/proved.mm $]

${
  $d k m z $.
  $d A k m z $.
  $d B k m z $.
  $d C k m z $.
  $d D k m z $.
  proofs.setmm.group-cancellation.element-of-its-coset $p |- ( ( ( ( A e. Grp /\ B e. ( SubGrp ` A ) ) /\ C e. ( Base ` A ) ) /\ D e. B ) -> ( C ( +g ` A ) D ) e. ( { C } ( LSSum ` A ) B ) ) $=
    ( cgrp wcel csubg cfv wa cbs cplusg co csn clsm vz cv wceq wrex vk simpr eqidd jca id oveq2d eqeq2d rspcev syl wb vm cbvrexvw bitri a1i mpbid wss w3a simpl eqid subgss 3jca gelcoset mpbird ) AEFZBAGHZFZIZCAJHZFZIZDBFZIZCDAKHZLZCMZBANHZLZFZVLCOPZVKLZQZOBRZVJVLCSPZVKLZQZSBRZVTVJVIVLVLQZIWDVJVIWEVHVITVJVLUAUBWCWESDBWADQZWBVLVLWFWADCVKWFUCUDUEUFUGWDVTUHVJWDVLCUIPZVKLZQZUIBRVTWCWISUIBWAWGQZWBWHVLWJWAWGCVKWJUCUDUEUJWIVSUIOBWGVQQZWHVRVLWKWGVQCVKWKUCUDUEUJUKULUMVJVBBVFUNZVGUOVPVTUHVJVBWLVGVJVHVBVHVIUPZVHVEVBVEVGUPZVEVBVBVBVDUPVBUCUGUGUGVJVDWLVJVHVDWMVHVEVDWNVBVDTUGUGVFBAVFUQURUGVJVHVGWMVEVGTUGUSOCBAVLUTUGVA $.
$}
