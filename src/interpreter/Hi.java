import java.io.*;
import java.awt.*;
import java.awt.image.*;
import java.awt.event.*;

class Hi extends Frame
{
	TextArea outputArea;
	Label   statusLabel;
	TextField inputField;
	StdIOProcess process;

	Hi()
	{
		super("hi");
		setSize(800, 600);

		inputField = new TextField(60);
		inputField.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent ae) {
				handleUserInput(inputField.getText());
			}});

/*
		interruptButton = new Button("Interrupt");
		interruptButton.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent ae) {
				interruptButton.setEnabled(false);
				statusLabel.setText("Interrupted by user (please wait)");
				process.destroy();
				while (!done)
					try { Thread.sleep(100); } catch (InterruptedException ie) {}
				statusLabel.setText("Done");
			}});
*/

	 	LogoCanvas logoCanvas = new LogoCanvas();

		final TextField runtimeInput = new TextField(60);
		runtimeInput.addActionListener(new ActionListener() {
			public void actionPerformed(ActionEvent ae) {
				if (process != null)
					process.sendInput(runtimeInput.getText());
			}});

		Panel northWestPanel = new Panel();
		northWestPanel.setLayout(new FlowLayout());
		northWestPanel.add(new Label("Expression: "));
		northWestPanel.add(inputField);
//		northWestPanel.add(interruptButton);
		northWestPanel.add(new Label("Runtime input: "));
		northWestPanel.add(runtimeInput);

		Panel northPanel = new Panel();
		northPanel.setLayout(new FlowLayout());
		northPanel.add(northWestPanel);
		northPanel.add(logoCanvas);

		outputArea = new TextArea(25, 80);
		outputArea.setFont(new Font("Monospaced", Font.PLAIN, 12));
		outputArea.setEditable(false);

		statusLabel = new Label();

		setLayout(new BorderLayout());
		add(northPanel, BorderLayout.NORTH);
		add(outputArea, BorderLayout.CENTER);
		add(statusLabel, BorderLayout.SOUTH);

		addWindowListener(new WindowAdapter() {
			public void windowClosing(WindowEvent we) {
				System.exit(0);
			}});

		setVisible(true);
	}

	public static void main(String args[])
	{
		try
		{
			new Hi();
		} catch (Exception e)
		{
			System.out.println("Uncaught exception: " + e);
			e.printStackTrace();
			System.exit(0);
		}
	}

	private final static String HI_TEMP_MODULE = "HiTemp";
	private final static String MAIN_FUNCTION = "interpreter_main";

	void handleUserInput(String input)
	{
		String hiTempFile = HI_TEMP_MODULE + ".hs";

		outputArea.append(">>> " + input + "\n");

		statusLabel.setText("Creating temporary file");

		try
		{
			PrintWriter printWriter =
				new PrintWriter(new FileWriter(hiTempFile), true);
			printWriter.println("module " + HI_TEMP_MODULE + " where");
			printWriter.println(MAIN_FUNCTION + " = " + input);
			printWriter.close();
		} catch (IOException e)
		{
			statusLabel.setText("Failed to write to " + hiTempFile);
			return;
		}

		statusLabel.setText("Running Helium compiler");

		process = new StdIOProcess("helium " + hiTempFile, outputArea);
		process.waitUntilDone();

		if (process.exitValue() != 0)
			return;

		statusLabel.setText("Running generated code");
		process = new StdIOProcess("lvmrun " + HI_TEMP_MODULE + ".lvm", outputArea);
		outputArea.append("\n");
	}

/*
	void setExecuting(boolean executing)
	{
		interruptButton.setEnabled(executing);
		inputField.setEditable(!executing);
		done = !executing;
	}
*/

}

class LogoCanvas extends Canvas
{
	 Image logoImage;

		LogoCanvas()
		{
			setSize(150, 45);
			logoImage = Toolkit.getDefaultToolkit().getImage("Logo.jpg");
			MediaTracker tracker = new MediaTracker(this);
			tracker.addImage(logoImage, 0);
			try {
				tracker.waitForAll();
			} catch (Exception e) {
				System.exit(0);
			}
	}

	public void paint(Graphics g)
	{
		g.drawImage(logoImage, 0, 0, null);
	}

}

class StdIOProcess implements Runnable
{
	TextArea outputArea;

	Process process;
	PrintWriter stdin;
	BufferedInputStream stdout;

	private final static int OUTPUT_WIDTH = 80;
	int count = 0;

	StdIOProcess(String command, TextArea outputArea)
	{
		Runtime runtime = Runtime.getRuntime();
		try {
			process = runtime.exec(command);
		} catch (IOException ie) {
			System.out.println("StdIOProcess.StdIOProcess: " + ie);
			System.exit(1);
		}

		this.outputArea = outputArea;
		stdin = new PrintWriter(process.getOutputStream(), true);
		stdout = new BufferedInputStream(process.getInputStream());
		Thread thread = new Thread(this);
		thread.start();
	}

	void sendInput(String s)
	{
		outputArea.append(s + "\n");
		stdin.println(s);
		count = 0;
	}

	public void run()
	{
		int ch;
		try {
			while ((ch = stdout.read()) != -1) {
				outputArea.append("" + (char) ch);
				if (ch == 10 || ch == 13)
					count = 0;
				else {
					count++;
					if (count % OUTPUT_WIDTH == 0) { outputArea.append("\n"); count = 0; }
				}
			}
		} catch (IOException ie) {
			System.out.println("StdIOProcess.run: " + ie);
			System.exit(1);
		}
	}

	void waitUntilDone()
	{
		try {
			process.waitFor();
		} catch (InterruptedException ie) {
			System.out.println("StdIOProcess.waitUntilDone: " + ie);
			System.exit(1);
		}
	}

	int exitValue()
	{
		return process.exitValue();
	}

}
