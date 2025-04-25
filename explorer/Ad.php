<?php
include 'i/head.php';
include 'i/pg.php';
$json = pgj("querymg " . $_GET["b"]);
if ($json->dbdata[0]->response != "pfgaddress") {
    header('Location: q.php?b=' . $_GET["b"]); die();
}
$v = $json->info;
include 'i/search.php';
?>
<h1>Proofgold Address</h1>
<table>
  <tr>
    <td><table><tr><th>address</th></tr><tr><td><?= $_GET["b"] ?></td></tr></table></td>
    <td><table><tr><th>total</th></tr><tr><td><?= (isset($v->total)) ? $v -> total : '-'; ?></td></tr></table></td>
    <td><table><tr><th>mg</th></tr><tr><td><?= mglinka($_GET["b"], "-") ?></td></tr></table></td>
<!--    <td><table><tr><th>ledgerroot</th></tr><tr><td><?= abbrv($v -> ledgerroot) ?></td></tr></table></td> -->
    <td><table><tr><th>conjpub</th></tr><tr><td><?= (isset($v->conjpub) ? abbrvaddr($v->conjpub) : "-") ?></td></tr></table></td>

                                                   </tr>
  <tr>
    <td colspan="4"><table><tr><th>current assets</th></tr><tr><td>
<?php 
  if (isset($v->currentassets)) {
    foreach ($v->currentassets as $vo) {
      echo oneasset($vo);
    }
  }
?>
</td></tr></table></td></tr>
  <tr>
    <td colspan="4"><table><tr><th>previous assets</th></tr><tr><td>
<?php 
  if (isset($v->previousassets)) {
    foreach ($v->previousassets as $vo) {
      echo oneasset($vo);
    }
  }
?>
</td></tr>

</table></td></tr></table></body></html>
