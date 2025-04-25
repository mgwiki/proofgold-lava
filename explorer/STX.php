<?php
include 'i/head.php';
include 'i/pg.php';
$json = pgj("querymg " . $_GET["b"]);
$v = $json->dbdata[0];
if ($v->type != "stx") {
    header('Location: q.php?b=' . $_GET["b"]); die();
}
include 'i/search.php';
?>
<h1>Proofgold Signed Transaction</h1>
<table><tr><td><table><tr><th>vin</th></tr><tr><td>
<?php
foreach ($v->tx->vin as $vi) {
	echo abbrvaddrasset($vi->address, $vi->assetid) . "<br/>\n";
}
?>
</td></tr></table></td></tr>
<tr><td><table><tr><th>vout</th></tr><tr><td>
<?php
foreach ($v->tx->vout as $vo) {
	echo onevout($vo);
}
?>
</td></tr></table></td></tr></table></body></html>
