$( tests/elaborator/records-products-gcds-preimages/a-product-of-reals, elaborated from tests/elaborator/records-products-gcds-preimages.proof by parley build.
   Nothing here is assumed.
   Checked against a set.mm of 51,256 assertions, sha256
   0d7fb3e59afff60f4cec2287cbb616bf651bbfbf2356a611a43a5c98b5e0462d. $)

$[ stdlib/definitions.mm $]

${
  $d A k $.
  $d B k $.
  tests.elaborator.records-products-gcds-preimages.a-product-of-reals $p |- ( ( ( A e. ZZ /\ 1 <_ A ) /\ B : ( 1 ... ( A + 1 ) ) --> RR ) -> prod_ k e. ( 1 ... ( A + 1 ) ) ( B ` k ) = ( prod_ k e. ( 1 ... A ) ( B ` k ) x. ( B ` ( A + 1 ) ) ) ) $=
    ( cz wcel c1 cle wbr wa caddc co cfz cr wf cv cfv w3a cuz 1z a1i simpl id syl simpr 3jca eluz2 sylibr cc jca ffvelcdm recn wceq fveq2d fprodp1 ) ADEZFAGHZIZFAFJKZLKZMBNZIZCOZBPZURBPCFAVAFDEZUOUPQAFRPEVAVDUOUPVDVASTVAUQUOUQUTUAZUQUOUOUOUPUAUOUBUCUCVAUQUPVEUOUPUDUCUEFAUFUGVAVBUSEZIZVCMEZVCUHEVGUTVFIVHVGUTVFVGVAUTVAVFUAUQUTUDUCVAVFUDUIUSMVBBUJUCVCUKUCVBURULZVBURBVIUBUMUN $.
$}
