<?php
include 'i/head.php';
include 'i/pg.php';
include 'i/search.php';
$o = "0";
$c = "0";
$incr = 20;
if (isset($_GET["o"])) { $o = $_GET["o"]; }
if (isset($_GET["c"])) { $c = $_GET["c"]; }
$jsono = pgj("queryopenbounties " . $o . " " . $incr);
$jsonc = pgj("querycollectedbounties " . $c . " " . $incr);
?>
<h1>Proofgold bounties</h1>
<h3><a href="https://github.com/ai4reason/Megalodon/tree/master/examples/pfgbounties">Description of bounties</a></h3>
<table><tr>
<td><table><tr><th>Open bounties</th></tr><tr><td>
<?php
foreach ($jsono->bounties as $d) {
    echo (isset($d->propid) ? (abbrvop($d->propid) . " ") : "") .
    (isset($d->npropid) ? (abbrvop($d->npropid) . " ") : "") .
    abbrvaddr($d->bountyaddress) . " " .
    (isset($d->npropaddr) ? abbrvaddr($d->npropaddr) . " " : "") .
    number_format($d->bountyvalue / 100000000000, 2) . "<br/>";
}
?>
<h3><a href="<?= "bounties.php?o=" . ((int) $o + $incr) . "&c=" . $c ?>">More open bounties</a></h3>
</td></tr></table></td>
<td><table><tr><th>Collected bounties</th></tr><tr><td>
<?php
foreach ($jsonc->bounties as $d) {
    echo (isset($d->propid) ? (abbrvop($d->propid) . " ") : "") .
    (isset($d->npropid) ? (abbrvop($d->npropid) . " ") : "") .
    abbrvaddr($d->bountyaddress) . " " .
    (isset($d->npropaddr) ? abbrvaddr($d->npropaddr) . " " : "") .
    number_format($d->bountyvalue / 100000000000, 2) . "<br/>";
}
?>
<h3><a href="<?= "bounties.php?o=" . $o . "&c=" . ((int) $c + $incr) ?>">More closed bounties</a></h3>
</td></tr></table></td></tr>
<tr>
     <td><table><tr><th>Open sum</th></tr><tr><td><?= number_format($jsono->totalsum / 100000000000, 2) ?></td></tr></table></td>
  <td><table><tr><th>Collected sum</th></tr><tr><td><?= number_format($jsonc->totalsum / 100000000000, 2) ?></td></tr></table></td>
</tr></table>

<table><tr><td><table><tr><td>
<div id="chart"></div>

<script>
    const color = d3.scaleOrdinal(d3.schemePaired);
    fetch('bounties.json').then(res => res.json()).then(data => {
      Sunburst()
        .data(data)
        .label('name')
        .size('size')
        .color((d, parent) => color(parent ? parent.data.name : null))
        .tooltipContent((d, node) => `Size: <i>${node.value}</i>`)
        (document.getElementById('chart'));
    });
</script>


</body></html>
