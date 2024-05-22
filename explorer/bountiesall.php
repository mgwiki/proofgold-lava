<?php
include 'i/pg.php';
$jsono = pgj("querybounties 0 20000");

$pat_rams = "/Ramsey/";
$pat_cstr = "/Cat_struct|Category_struct/";
$pat_raim = "/RandomlyGeneratedAIM/";
$pat_oeis = "/oeis-A/";
$pat_cest = "/CategorySet/";
$pat_preamb = "/Preamble/";
$pat_surr = "/surreal.*ConjsWithBounties/";
$pat_miz = "/t3_xregular/";
$pat_form = "/form100/";
$pat_abstrhf = "/AbstrHF/";
$pat_hosc = "/HOSetConstr/";
$pat_diom = "/DiophantineMod[12]/";
$pat_dio = "/Diophantine[12]/";
$pat_combu = "/CombUnif/";
$pat_houni = "/HOUnif/";
$pat_rand = "/Random[123]/";
$pat_qbf = "/QBF_TM/";
$pat_mizar = "/mizar/";


?>
<pre>
<?php
foreach ($jsono->bounties as $d) {
    $l = (isset($d->propid) ? (mglinki($d->propid, "-")) : "-");
    if ($l == "-") { $l = (isset($d->npropid) ? (mglinki($d->npropid, "-")) : "-"); }
    if ($l == "-") { $l = mglinka($d->bountyaddress, "-"); }
    if ($l == "-") { $l = (isset($d->npropaddr) ? mglinka($d->npropaddr,"-") : "-"); }
if (preg_match($pat_rams, $l)) { $l = "Ramsey"; }
if (preg_match($pat_cstr, $l)) { $l = "CatStruct"; }
if (preg_match($pat_raim, $l)) { $l = "Random AIM"; }
if (preg_match($pat_oeis, $l)) { $l = "OEIS"; }
if (preg_match($pat_cest, $l)) { $l = "CatSet"; }
if (preg_match($pat_preamb, $l)) { $l = "Preamble"; }
if (preg_match($pat_surr, $l)) { $l = "Surreal"; }
if (preg_match($pat_miz, $l)) { $l = "Mizar"; }
if (preg_match($pat_form, $l)) { $l = "Form100"; }
if (preg_match($pat_abstrhf, $l)) { $l = "AbstrHF"; }
if (preg_match($pat_hosc, $l)) { $l = "HOSetConstr"; }
if (preg_match($pat_dio, $l)) { $l = "Diophantine"; }
if (preg_match($pat_diom, $l)) { $l = "DiophantineMod"; }
if (preg_match($pat_combu, $l)) { $l = "CombUnif"; }
if (preg_match($pat_houni, $l)) { $l = "HOUnif"; }
if (preg_match($pat_rand, $l)) { $l = "Random123"; }
if (preg_match($pat_qbf, $l)) { $l = "QBF"; }
if (preg_match($pat_mizar, $l)) { $l = "Mizar"; }

echo $l . ", " . ($d->spent ? "C" : "O") . ", " . number_format($d->bountyvalue / 100000000000, 2) . "\n";
}
?>
</pre>
