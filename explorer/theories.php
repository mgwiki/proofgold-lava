<?php
include 'i/head.php';
include 'i/pg.php';
$json = pgj("theories");
include 'i/search.php';
?>
<h1>Proofgold Theories</h1>
<table>
<?php
foreach ($json as $t ) {
    $name = ($t->names == []) ? $t -> theoryid : $t->names[0];
    $as = isset($t->assetid) ? abbrvasset1($t->assetid) : "-";
    $ad = isset($t->addr) ? abbrvaddr($t->addr) : "-";
    $pub = isset($t->publisher) ? abbrvaddr($t->publisher) : "-";
    echo "<tr><td style='padding-right: 0; padding-left: 0;'><table><tr><th>Theory</th></tr><tr><td>" . $name . "</td></tr></table></td>";
    echo "<td style='padding-right: 0;  padding-left: 0;'><table><tr><th>Asset</th></tr><tr><td>" . $as . "</td></tr></table></td>";
    echo "<td style='padding-right: 0; padding-left: 0;'><table><tr><th>Address</th></tr><tr><td>" . $ad . "</td></tr></table></td>";
    echo "<td style='padding-right: 0; padding-left: 0;'><table><tr><th>Publisher</th></tr><tr><td>" . $pub . "</td></tr></table></td></tr>";
//    echo "Theory " . $name . " Asset " . $as . " Address " . $ad . " Published by " . $pub . "<br/>\n";
}
?>
</table></body></html>

