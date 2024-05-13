<?php
include 'i/pg.php';
$q = $_GET["b"];

if ($q == "") {
    header('Location: index.php'); die ();
} else if (strlen ($q) > 34 || is_numeric($q)) {
    $json = pgj("querymg " . $q);
    if (! (isset ($json->response))) {
        echo "<h3>No response obtained!</h3>";
    } else if ($json->response == 'known') {
        foreach ($json->dbdata as $v) {
            if ($v->type == 'block') {
                header('Location: Bl.php?b=' . $q);
            } else if ($v->type == 'asset' || $v->type == 'assetid') {
                header('Location: As.php?b=' . $q);
            } else if ($v->type == 'stx') {
                header('Location: STX.php?b=' . $q); die();
            } else if ($v->type == 'termroot') {
                header('Location: TR.php?b=' . $q); die();
            } else if ($v->type == 'obj' || $v->type == 'prop') {
                header('Location: OP.php?b=' . $q); die();
            } else if ($v->type == 'termid') {
                header('Location: Ad.php?b=' . $v->termaddress); die();
            } else if ($v->type == 'ctreeelt') {
                header('Location: qq.php?b=' . $q);
            } else {
                echo "<pre>";
                echo (var_export($v));
            }
        }
    } else if ($json->response == 'unknown') {
        echo "<h2>No information about " . $q . "</h2>";
    } else if ($json->response == 'pfgaddress') {
        header('Location: Ad.php?b=' . $q);
    } else {
        echo "<h2>Unknown Response!</h2>" . $json->response;
    }
} else {
    if (($handle = fopen("/home/cezary/.proofgold/mglegenddefault", "r")) !== FALSE) {
        while (($data = fgetcsv($handle, 1000, " ")) !== FALSE) {
            $num = count($data);
            if (count($data) == 3 && ($data[0] == "P" || $data[0] == "O")) {
                if ($data[2] == $q) {
                    header('Location: q.php?b=' . $data[1]);
                    die ();
                }
            }
        }
        echo "Unknown Query!";
        fclose($handle);
    }
}

?>
</body>
