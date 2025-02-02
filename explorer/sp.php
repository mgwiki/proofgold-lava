<?php
include 'i/head.php';
$pu = $_GET["pu"];
$it = $_GET["it"];
if (strpos($pu, "PU") !== 0) {
    echo "Error: The agument is invalid";
    exit;
}
include 'i/pg.php';
$p1 = isset($_GET["p1"]) ? $_GET["p1"] : 0;
$p2 = isset($_GET["p2"]) ? $_GET["p2"] : 0;
//$temp = fopen("tst.txt", "a");
//fwrite($temp, $_SERVER['REMOTE_ADDR'] . " PU: " . $pu . " IT: " . $it . "\n");
//fclose($temp);
$p = pg("displaysubpfhtml " . $pu . " " . $it . " 0 " . $p1 . " " . $p2 . " 500");
include 'i/search.php';
?>

<script>
function g(element, pu2, i2, p1, p2) {
    window.location.href = "sp.php?pu=<?= $pu ?>&it=<?= $it ?>&p1=" + p1 + "&p2=" + p2;
}
</script>

<h1>Proofgold Proof</h1>
<table><tr>
    <td><table><tr><th>pf</th></tr><tr><td style="text-align: left"><?= $p ?></td></tr></table></td>
</tr></table></body></html>
