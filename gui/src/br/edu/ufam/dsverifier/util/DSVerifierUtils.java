package br.edu.ufam.dsverifier.util;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.InputStream;
import java.io.InputStreamReader;

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
}
