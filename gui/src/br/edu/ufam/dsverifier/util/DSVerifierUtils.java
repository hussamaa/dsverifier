package br.edu.ufam.dsverifier.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

import javafx.geometry.Insets;
import javafx.scene.control.TextField;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Region;

import org.controlsfx.control.RangeSlider;

public class DSVerifierUtils {

	private static DSVerifierUtils instance;

	private DSVerifierUtils() {
	}

	public static DSVerifierUtils getInstance() {
		if (instance == null) {
			instance = new DSVerifierUtils();
		}
		return instance;
	}

	public String callCommandLine(String commandLine) throws IOException,
			InterruptedException {
		Process p = Runtime.getRuntime().exec(commandLine);
		InputStream inputStream = p.getInputStream();
		InputStreamReader inputStreamReader = new InputStreamReader(inputStream);
		BufferedReader bufferedReader = new BufferedReader(inputStreamReader);
		StringBuilder output = new StringBuilder();
		String line;
		while ((line = bufferedReader.readLine()) != null) {
			System.out.println(line); // it prints all at once after command has
										// been executed.
			output.append(line + "\n");
		}
		p.waitFor();
		return output.toString();
	}
	
	public Region createHorizontalSlider() {
        final TextField minField = new TextField();
        minField.setPrefColumnCount(2);
        final TextField maxField = new TextField();
        maxField.setPrefColumnCount(2);
 
        final RangeSlider hSlider = new RangeSlider(-10, 10, -1, 1);
        hSlider.setShowTickMarks(true);
        hSlider.setShowTickLabels(true);
        hSlider.setBlockIncrement(10);
        hSlider.setPrefWidth(100);
 
        minField.setText("" + hSlider.getLowValue());
        maxField.setText("" + hSlider.getHighValue());
 
        minField.setEditable(false);
        minField.setPromptText("Min");
 
        maxField.setEditable(false);
        maxField.setPromptText("Max");
 
        minField.textProperty().bind(hSlider.lowValueProperty().asString("%.0f"));
        maxField.textProperty().bind(hSlider.highValueProperty().asString("%.0f"));
 
        HBox box = new HBox(10);
        box.getChildren().addAll(minField, hSlider, maxField);
        box.setPadding(new Insets(20,0,0,20));
        box.setFillHeight(false);
 
        return box;
    }
}
