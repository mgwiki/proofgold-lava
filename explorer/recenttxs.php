<?php
include 'i/head.php';
include 'i/pg.php';
$query = "recenttxs";
if (isset($_GET["b"])) {
  $query .= " " . $_GET["b"];
}
$json = pgj($query);
include 'i/search.php';
?>
<h1>Proofgold Recent Txs</h1>
<table><tr><td><table><tr><td>
<?php
$c = count($json->recenttxs); // foreach but reversed
while ($c) {
    $d=$json->recenttxs[--$c];
    echo ahrefblock($d->height) . " " . gmdate("Y-m-d\TH:i:s\Z", $d->time) . " " . abbrvstx($d->stx) . "<br/>";
}
if (isset($json->prevblock)) {
    echo "More <a href=\"recenttxs.php?b=" . $json->prevblock . "\">recent txs</a>";
}
?>
</td></tr></table></td></tr></table></body></html>

