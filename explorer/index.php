<?php
include 'i/head.php';
include 'i/pg.php';
include 'i/search.php';
$json = pgj("querybestblock");
//var_export($json);
?>
<h1>Proofgold explorer</h1>
<table><tr>
  <td><table><tr><th><h4><a href="bounties.php">Bounties</a>: 9190</a> worth 278'234 PG</h4></th></tr><tr><td><div id="chart"></div></td></tr></table></td>
<td><table><tr><th><h4>Recent Claimed</h4></th></tr><tr><td>
 <div style="height: 300px;"><div align="left"><pre>
<?php include 'i/mockthm.php'; ?>
  </pre></div>
    <div align=right><font size=-2>see doc <?= abbrvaddr('PUUQgo4kCpPFsyheYGxf1dZyddFed5u2c2z') ?></div>



    </div>
</td></tr></table></td>
</tr>
</table>
<hr/>
  <table>
  <tr>
    <td><table><tr><th>Blocks</th></tr><tr><td><?= ahrefblock($json->height) ?></td></tr></table></td>
    <td><table><tr><th>Circulation</th></tr><tr><td><?= 5000 * 50 + ($json->height - 5000) * 25 ?></td></tr></table></td>
  </tr><tr>
    <td><table><tr><th>Addresses</th></tr><tr><td><?= $json->numaddresses ?></td></tr></table></td>
    <td><table><tr><th>Transactions</th></tr><tr><td><?= $json->numtxs ?></td></tr></table></td>
  </tr><tr>
    <td><table><tr><th><a href="map.php">Recent Connections</a> (Currently <?= strtok(pgopen("getpeerinfo"),"\n") ?>)</th></tr><tr><td><a href="map.php"><img src="map.jpg"/></a> </td></tr></table></td>
<!--    <td><table><tr><th>Addresses</th></tr><tr><td></td></tr></table></td>-->
    <td><table><tr><th>Genesis</th></tr><tr><td>June 2020: <?= ahrefblock(1) ?></td></tr></table></td>
  </tr><tr>
    <td><table><tr><th>Recent</th></tr><tr><td><a href="recenttxs.php">Transactions</a></td></tr></table></td>
<!--    <td><table><tr><th>Recent</th></tr><tr><td><a href="recentdocs.php">Documents</a></td></tr></table></td>-->
    <td><table><tr><th>Recent</th></tr><tr><td><a href="recentthms.php">Theorems</a></td></tr></table></td>
  </tr>
  </tr><tr>
<!--  <td><table><tr><th>Recent</th></tr><tr><td><a href="msg.php">Messages</a></td></tr></table></td>
  <td><table><tr><th>Recent</th></tr><tr><td><a href="listen.php">Listeners</a></td></tr></table></td>-->
  <td><table><tr><th>All</th></tr><tr><td><a href="theories.php">Theories</a></td></tr></table></td>
  <td><table><tr><th>Recent</th></tr><tr><td><a href="recentbounties.php">Bounties</a></td></tr></table></td>-->
   </tr>
</table>

<!--
  <table width=90%>
<tr><td width=50%><h4>Upload Conjecture</h4>
<textarea id="qwe" name="qwe2" rows="4" cols="50">Conjecture: Repl (Power (Power y))
  (fun w:set => If_i (y :e w) y z) = UPair y z
    -> UPair y z :e x.</textarea><input type="submit" value="Go!" />
</td><td width=50%><h4>Upload Proof</h4>
  <textarea id="asd" name="asd2" rows="4" cols="50"></textarea><input type="submit" value="Go!" />
</td>
</tr>

</table>
-->

<table><tr><td>Documentation and Clients: <a href="https://prfgld.github.io/">Original Proofgold</a>; <a href="https://github.com/dalcoder/proofgoldlite">ProofGoldLite</a>; <a href="http://proofgold.net/">ProofGold Lava</a></td></tr></table>

<!--
<h3>Buy Offers</h3>
<?= nl2br(pg("buyoffers")) ?>
 -->
 
 </center>

<script>
  function fetchCSV() {
      const xhr = new XMLHttpRequest();
      xhr.open('GET', "price.csv", false); // 'false' makes the request synchronous
      xhr.send(null);
      if (xhr.status === 200) {
          const text = xhr.responseText;
          const result = Papa.parse(text, { header: true, dynamicTyping: true });
          const data = result.data.map(row => ({
              x: row.x,
              y: row.y
          }));
          return data;
      } else {
          console.error('Error fetching CSV:', xhr.status, xhr.statusText);
      }
  }
  function getTimeSeriesData() {
      return [
          { x: '1711738677', y: 0.030033 },
          { x: '1712078680', y: 0.035091 },
          { x: '1712662593', y: 0.040099 },
      ];
  }
  //var data = getTimeSeriesData();
  var data = fetchCSV();
  const dataf = data.filter(entry => entry.x !== null);
  const dataWithDates = dataf.map(point => {
      const date = new Date(point.x * 1000); // Multiply by 1000 to convert seconds to milliseconds
      const year = date.getUTCFullYear();
      const month = String(date.getUTCMonth() + 1).padStart(2, '0'); // Months are 0-based, so add 1 and pad with leading zeros if needed
      const day = String(date.getUTCDate()).padStart(2, '0'); // Pad with leading zeros if needed

      return {
          x: `${year}-${month}-${day}`,
          y: point.y,
      };
  });
  var xValues = dataWithDates.map(point => point.x);
  var yValues = dataWithDates.map(point => point.y);
  var trace = {
      x: xValues,
      y: yValues,
      type: 'scatter',
      mode: 'lines+markers',
      marker: {
          color: 'blue'
      },
      line: {
          width: 3 // Set the line width to 3 pixels
      }
  };

  var layout = {
      margin: {
          l: 40,
          r: 20,
          t: 20,
          b: 30
      }
  };
  Plotly.newPlot('timeSeriesGraph', [trace], layout);
  window.addEventListener('resize', function() {
      Plotly.relayout('timeSeriesGraph', {
          width: 30,
          height: 1
      });
      var width = document.getElementById('timeSeriesGraph').clientWidth;
      var height = document.getElementById('timeSeriesGraph').clientHeight;
      Plotly.relayout('timeSeriesGraph', {
          width: width,
          height: height
      });
      Plotly.Plots.resize('timeSeriesGraph');
  });
</script>

<script>
    const color = d3.scaleOrdinal(d3.schemePaired);
    fetch('bounties.json').then(res => res.json()).then(data => {
      Sunburst()
        .data(data)
        .label('name')
        .size('size')
        .width('300')        .height('300')
        .color((d, parent) => color(parent ? parent.data.name : null))
        .tooltipContent((d, node) => `Size: <i>${node.value}</i>`)
        (document.getElementById('chart'));
    });
</script>

</body></html>
