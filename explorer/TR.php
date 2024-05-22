<?php
include 'i/head.php';
include 'i/pg.php';
$json = pgj("querymg " . $_GET["b"]);
$lastthy = "";
include 'i/search.php';
?>
<h1>Proofgold Term Root Disambiguation </h1>
<?php
$theories = [];
$tid = [];
$thf = [];
foreach ($json->dbdata as $tr) {
    if ($tr->type == "termroot") {
        if (isset($tr->theory)) {
            if (!array_key_exists($tr->theory, $theories)) {
                $theories[$tr->theory] = []; // Initialize an empty array for this theory
            }
            $theories[$tr->theory][] = $tr; // Add the current item to the array for this theory
        } else {
            $thf = $tr;
        }
    } else if ($tr->type == "termid") {
        $tid = $tr;
    } else {
        echo "Not a Term Root!"; die();
    }
}

foreach ($theories as $t => $items) {
    $tr=$items[0];
    echo '<table><tr><td colspan="3"><table><tr><td>' . $tr->trmpres . "</td></tr></table></td></tr>\n";
    echo "<tr><td><table><tr><th>as obj</th></tr><tr><td>" . (isset($tr->correspondingobj) ? abbrvop($tr->correspondingobj) : "-") . "</td></tr></table></td>\n";
    echo "<td><table><tr><th>as prop</th></tr><tr><td>" . (isset($tr->correspondingprop) ? abbrvop($tr->correspondingprop) : "-") . "</td></tr></table></td>\n";
    echo '<td><table><tr><th>theory</th></tr><tr><td>' . abbrvthyandname($tr) . "</td></tr></table></td></tr>\n";
    echo '<tr><td colspan="3"><table><tr><th>stx</th></tr><tr><td>';
    foreach ($items as $i) {
        echo abbrvstx($i->tx) . " ";
    }
    echo "</td></tr></table></td></tr></table>\n";
}

if ($thf != []) {
    echo "<table><tr><td><table><tr><th>hf term</th></tr><tr><td>"; var_export($thf); echo "</td></tr></table></td></tr></table>";
}

if ($tid != []) {
    echo "<table><tr><td><table><tr><th>address</th></tr><tr><td>" . abbrvaddr($tid->termaddress) . "</td></tr></table></td></tr></table>";
}
?>

</body></html>
