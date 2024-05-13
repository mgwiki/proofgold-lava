<?php
include 'i/head.php';
include 'i/pg.php';
$json = pgj("querymg " . $_GET["b"]);
$o = $json->dbdata[0];
if ($o->type == "termid") {
    header('Location: Ad.php?b=' . $o->termaddress); die();
}
include 'i/search.php';
?>
<h1>Proofgold <?= ($o->type == "prop") ? "Proposition" : "Object" ?> </h1>
<table><tr><td colspan="3"><table><tr><td><?= $o->trmpres ?></td></tr></table></td></tr>
  <tr>
       <td><table><tr><th>type</th></tr><tr><td><?= ($o->type == "prop") ? "prop" : $o->stppres  ?></td></tr></table></td>
       <td><table><tr><th>theory</th></tr><tr><td><?= abbrvthyandname($o) ?></td></tr></table></td>
       <td><table><tr><th>term addr</th></tr><tr><td><?= isset($o->termaddress) ? abbrvaddr($o->termaddress) : "-" ?></td></tr></table></td>
  </tr>
  <tr>
    <td><table><tr><th>creator</th></tr><tr><td>
<?php
if (($o->type == "prop" && isset($o->creatorasprop)) || ($o->type != "prop" && isset($o->creatorasobj))) {
    $oc = ($o->type == "prop") ? $o->creatorasprop : $o->creatorasobj;
    echo ahrefblock($oc->bday) . " " . abbrvaddrasset($oc->creatoraddr,$oc->assetid);
}
?></td></tr></table></td>
   <td><table><tr><th>owner</th></tr><tr><td>
<?php
if (($o->type == "prop" && isset($o->ownerasprop)) || ($o->type != "prop" && isset($o->ownerasobj))) {
    $oo = ($o->type == "prop") ? $o->ownerasprop : $o->ownerasobj;
    echo ahrefblock($oo->bday) . " " . abbrvaddrasset($oo->owneraddr,$oo->assetid);
}
?></td></tr></table></td>
    <td><table><tr><th>term root</th></tr><tr><td><?= abbrv($o->termroot)  ?></td></tr></table></td>
  </tr>
  <tr>
       <td><table><tr><th>first pub addr</th></tr><tr><td><?= isset($o->firstpubaddr) ? abbrv($o->firstpubaddr) : "-" ?></td></tr></table></td>
<td><table><tr><th>mg</th></tr><tr><td>
     <?= mglinki($_GET["b"], "-") ?>
</td></tr></table></td>
  </tr>


</table></td></tr></table></body></html>
