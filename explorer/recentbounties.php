<?php
include 'i/head.php';
include 'i/pg.php';
include 'i/search.php';
$o = "0";
$c = "0";
$incr = 20;
if (isset($_GET["o"])) { $o = $_GET["o"]; }
if (isset($_GET["c"])) { $c = $_GET["c"]; }
$jsono = pgj("queryrecentplacedbounties " . $o . " " . $incr);
$jsonc = pgj("queryrecentcollectedbounties " . $c . " " . $incr);
?>
<h1>Proofgold recent bounties</h1>
<table><tr>
<td><table><tr><th>Recently placed bounties</th></tr><tr><td>
<?php
foreach ($jsono->bounties as $d) {
    showbounty($d);
}
?>
<h3><a href="<?= "recentbounties.php?o=" . ((int) $o + $incr) . "&c=" . $c ?>">More recent placed</a></h3>
</td></tr></table></td>
<td><table><tr><th>Recently collected bounties</th></tr><tr><td>
<?php
foreach ($jsonc->bounties as $d) {
    showbounty($d);
}
?>
<h3><a href="<?= "recentbounties.php?o=" . $o . "&c=" . ((int) $c + $incr) ?>">More recent collected</a></h3>
</td></tr></table></td></tr>
</table>
