"""PixSort — 画像並び替え＆リネームツール

ディレクトリ内のPNG画像をD&Dで並び替え、連番(010, 020, 030...)でリネームする。
"""

import hashlib
import json
import os
import tkinter as tk
from concurrent.futures import ThreadPoolExecutor
from tkinter import filedialog, messagebox
from tkinterdnd2 import DND_FILES, TkinterDnD
from PIL import Image, ImageTk

THUMB_SIZES = (80, 150, 250)  # 小・中・大
THUMB_SIZE_DEFAULT_INDEX = 1  # 中（150）
CELL_PADDING = 10
LABEL_HEIGHT = 20
AUTO_SCROLL_ZONE = 40
AUTO_SCROLL_INTERVAL = 30
CONFIG_PATH = os.path.join(os.path.dirname(os.path.abspath(__file__)), "config.json")
CACHE_DIR = os.path.join(os.path.dirname(os.path.abspath(__file__)), "cache")
CACHE_MAX_BYTES = 200 * 1024 * 1024  # 200MB
POLL_INTERVAL_MS = 16  # ~60fps ポーリング


def _cache_key(abs_path, mtime, file_size):
    """キャッシュキーを生成（sha256ハッシュ）"""
    raw = f"{abs_path}|{mtime}|{file_size}"
    return hashlib.sha256(raw.encode("utf-8")).hexdigest()


def _cache_get(cache_dir, key, thumb_size):
    """キャッシュからサムネイルを読み込む。ヒットすればPIL Image、ミスならNone"""
    path = os.path.join(cache_dir, f"{key}_{thumb_size}.jpg")
    if not os.path.exists(path):
        return None
    try:
        img = Image.open(path)
        img.load()
        return img
    except Exception:
        return None


def _cache_put(cache_dir, key, thumb_size, pil_image):
    """サムネイルをキャッシュに保存（JPEG quality=90）"""
    try:
        img = pil_image
        if img.mode == "RGBA":
            bg = Image.new("RGB", img.size, (43, 43, 43))
            bg.paste(img, mask=img.split()[3])
            img = bg
        elif img.mode != "RGB":
            img = img.convert("RGB")
        path = os.path.join(cache_dir, f"{key}_{thumb_size}.jpg")
        img.save(path, "JPEG", quality=90)
    except Exception:
        pass


def _cleanup_cache(cache_dir, max_bytes):
    """キャッシュディレクトリが max_bytes を超えていたら古いファイルから削除"""
    try:
        files = []
        for name in os.listdir(cache_dir):
            if not name.endswith(".jpg"):
                continue
            fp = os.path.join(cache_dir, name)
            st = os.stat(fp)
            files.append((fp, st.st_size, st.st_mtime))
    except Exception:
        return

    total = sum(size for _, size, _ in files)
    if total <= max_bytes:
        return

    # mtime が古い順にソートして削除
    files.sort(key=lambda x: x[2])
    for fp, size, _ in files:
        if total <= max_bytes:
            break
        try:
            os.remove(fp)
            total -= size
        except Exception:
            pass


def _process_image_worker(path, thumb_sizes, cache_dir):
    """ワーカースレッドでサムネイルを生成（PIL Imageを返す）"""
    filename = os.path.basename(path)
    try:
        stat = os.stat(path)
        key = _cache_key(os.path.abspath(path), stat.st_mtime, stat.st_size)
    except Exception:
        key = None

    pil_images = []
    source_img = None

    for size in thumb_sizes:
        cached = _cache_get(cache_dir, key, size) if key else None
        if cached is not None:
            pil_images.append(cached)
            continue

        # ソース画像を遅延読み込み（初回のみ）
        if source_img is None:
            try:
                source_img = Image.open(path)
                source_img.load()
            except Exception:
                source_img = False  # 読み込み失敗フラグ

        if source_img is False:
            pil_images.append(Image.new("RGB", (size, size), (80, 80, 80)))
            continue

        img = source_img.copy()
        img.thumbnail((size, size), Image.LANCZOS)
        pil_images.append(img)

        if key:
            _cache_put(cache_dir, key, size, img)

    return (path, filename, pil_images)


class ImageSorterApp:
    def __init__(self, root):
        self.root = root
        self.root.title("PixSort — 画像並び替え＆リネーム")
        self.root.geometry("900x700")
        self.root.minsize(400, 300)

        self.directory = None
        # list of {"path": str, "name": str, "thumbs": [ImageTk x3], "thumb": ImageTk}
        self.images = []
        self._thumb_size_idx = THUMB_SIZE_DEFAULT_INDEX
        self.drag_index = None
        self.insert_index = None
        self.drag_ghost = None
        self._auto_scroll_after_id = None
        self._loading = False
        self._load_cancelled = False
        self._executor = None
        self._futures = {}
        self._results = None
        self._completed_count = 0
        self._total_count = 0
        self._viewer_win = None
        self._split_mode = False
        self._active_canvas = None
        self._drag_canvas = None

        self._build_ui()
        self._setup_folder_dnd()

        # キャッシュクリーンアップ
        os.makedirs(CACHE_DIR, exist_ok=True)
        _cleanup_cache(CACHE_DIR, CACHE_MAX_BYTES)

        # 前回フォルダの自動読み込み
        last_folder = self._load_config()
        if last_folder and os.path.isdir(last_folder):
            self.root.after(100, lambda: self._open_folder(last_folder))

    @property
    def _thumb_size(self):
        return THUMB_SIZES[self._thumb_size_idx]

    # ── Config persistence ────────────────────────────────

    def _load_config(self):
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
            return data.get("last_folder")
        except Exception:
            return None

    def _save_config(self):
        data = {}
        try:
            with open(CONFIG_PATH, "r", encoding="utf-8") as f:
                data = json.load(f)
        except Exception:
            pass
        data["last_folder"] = self.directory
        try:
            with open(CONFIG_PATH, "w", encoding="utf-8") as f:
                json.dump(data, f, ensure_ascii=False, indent=2)
        except Exception:
            pass

    def _build_ui(self):
        # Top bar
        top = tk.Frame(self.root)
        top.pack(fill=tk.X, padx=8, pady=6)

        self.btn_select = tk.Button(top, text="フォルダ選択", command=self._select_folder)
        self.btn_select.pack(side=tk.LEFT)

        self.lbl_dir = tk.Label(top, text="(未選択)", anchor=tk.W)
        self.lbl_dir.pack(side=tk.LEFT, padx=8, fill=tk.X, expand=True)

        self.btn_split = tk.Button(top, text="分割", command=self._toggle_split)
        self.btn_split.pack(side=tk.RIGHT)

        self.btn_zoom_in = tk.Button(top, text="＋", width=2, command=self._zoom_in)
        self.btn_zoom_in.pack(side=tk.RIGHT, padx=(0, 4))

        self.btn_zoom_out = tk.Button(top, text="－", width=2, command=self._zoom_out)
        self.btn_zoom_out.pack(side=tk.RIGHT, padx=(0, 2))

        # Scrollable canvas area
        mid = tk.Frame(self.root)
        mid.pack(fill=tk.BOTH, expand=True, padx=8)

        # Left panel
        self._panel_l = tk.Frame(mid)
        self._panel_l.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.canvas = tk.Canvas(self._panel_l, bg="#2b2b2b", highlightthickness=0)
        self.scrollbar = tk.Scrollbar(self._panel_l, orient=tk.VERTICAL, command=self.canvas.yview)
        self.canvas.configure(yscrollcommand=self.scrollbar.set)
        self.scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Divider (hidden initially)
        self._divider = tk.Frame(mid, width=2, bg="#555555")

        # Right panel (hidden initially)
        self._panel_r = tk.Frame(mid)

        self.canvas_r = tk.Canvas(self._panel_r, bg="#2b2b2b", highlightthickness=0)
        self.scrollbar_r = tk.Scrollbar(self._panel_r, orient=tk.VERTICAL, command=self.canvas_r.yview)
        self.canvas_r.configure(yscrollcommand=self.scrollbar_r.set)
        self.scrollbar_r.pack(side=tk.RIGHT, fill=tk.Y)
        self.canvas_r.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        # Bind events to both canvases
        for c in (self.canvas, self.canvas_r):
            c.bind("<ButtonPress-1>", lambda e, cv=c: self._on_press(e, cv))
            c.bind("<B1-Motion>", self._on_drag)
            c.bind("<ButtonRelease-1>", self._on_drop)
            c.bind("<Configure>", self._on_canvas_resize)
            c.bind("<MouseWheel>", lambda e, cv=c: self._on_mousewheel(e, cv))
            c.bind("<Control-MouseWheel>", self._on_ctrl_mousewheel)
            c.bind("<Double-Button-1>", lambda e, cv=c: self._on_double_click(e, cv))

        # Bottom bar
        bottom = tk.Frame(self.root)
        bottom.pack(fill=tk.X, padx=8, pady=6)

        self.btn_rename = tk.Button(
            bottom, text="リネーム実行", command=self._do_rename, state=tk.DISABLED
        )
        self.btn_rename.pack()

        self.btn_cancel = tk.Button(bottom, text="キャンセル", command=self._cancel_loading)
        # 初期状態では非表示（読み込み中のみpack）

    # ── Split toggle ─────────────────────────────────────────

    def _toggle_split(self):
        self._split_mode = not self._split_mode
        if self._split_mode:
            self._divider.pack(side=tk.LEFT, fill=tk.Y, padx=1)
            self._panel_r.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
            self.btn_split.config(text="統合")
        else:
            self._panel_r.pack_forget()
            self._divider.pack_forget()
            self.btn_split.config(text="分割")
        if not self._loading:
            self._draw_grid()

    def _visible_canvases(self):
        """現在表示中のキャンバスのリストを返す"""
        if self._split_mode:
            return [self.canvas, self.canvas_r]
        return [self.canvas]

    # ── Folder D&D from Explorer ──────────────────────────────

    def _setup_folder_dnd(self):
        self.root.drop_target_register(DND_FILES)
        self.root.dnd_bind("<<Drop>>", self._on_folder_drop)

    def _on_folder_drop(self, event):
        path = event.data.strip()
        # tkdnd wraps paths with spaces in {}
        if path.startswith("{") and path.endswith("}"):
            path = path[1:-1]
        if os.path.isdir(path):
            self._open_folder(path)

    # ── Folder / image loading ──────────────────────────────

    def _select_folder(self):
        d = filedialog.askdirectory(title="画像フォルダを選択")
        if not d:
            return
        self._open_folder(d)

    def _open_folder(self, path):
        self.directory = path
        self.lbl_dir.config(text=path)
        self._save_config()
        self._load_images()

    def _load_images(self):
        # 既存の executor があればシャットダウン
        if self._executor is not None:
            self._executor.shutdown(wait=False)
            self._executor = None
            self._futures.clear()

        self.images.clear()
        files = sorted(
            f for f in os.listdir(self.directory)
            if f.lower().endswith(".png")
        )

        if not files:
            self.btn_rename.config(state=tk.DISABLED)
            self._draw_grid()
            return

        total = len(files)
        self._results = [None] * total
        self._completed_count = 0
        self._total_count = total

        # 読み込み中状態
        self._loading = True
        self._load_cancelled = False
        self.btn_select.config(state=tk.DISABLED)
        self.btn_rename.config(state=tk.DISABLED)
        self.btn_cancel.pack()
        self._draw_progress(0, total)

        # ThreadPoolExecutor で並列処理
        workers = max(1, (os.cpu_count() or 4) - 1)
        self._executor = ThreadPoolExecutor(max_workers=workers)
        self._futures = {}
        for idx, f in enumerate(files):
            path = os.path.join(self.directory, f)
            future = self._executor.submit(
                _process_image_worker, path, THUMB_SIZES, CACHE_DIR
            )
            self._futures[future] = idx

        self.root.after(POLL_INTERVAL_MS, self._poll_futures)

    def _cancel_loading(self):
        self._load_cancelled = True

    def _finish_loading(self):
        """読み込み完了・キャンセル共通の後処理"""
        self._loading = False
        self.btn_cancel.pack_forget()
        self.btn_select.config(state=tk.NORMAL)
        if self._executor is not None:
            self._executor.shutdown(wait=False)
            self._executor = None
        self._futures.clear()

    def _poll_futures(self):
        if self._load_cancelled:
            # キャンセル: 全Future取消→状態リセット
            for future in self._futures:
                future.cancel()
            self.images.clear()
            self._results = None
            self.directory = None
            self.lbl_dir.config(text="(未選択)")
            self.btn_rename.config(state=tk.DISABLED)
            self._finish_loading()
            self.canvas.delete("all")
            self.canvas_r.delete("all")
            return

        # 完了したFutureを回収（1回のポーリングで最大10個）
        done_futures = [f for f in self._futures if f.done()]
        batch = done_futures[:10]

        for future in batch:
            idx = self._futures.pop(future)
            try:
                path, filename, pil_images = future.result()
                # PIL → ImageTk.PhotoImage 変換（メインスレッド）
                thumbs = [ImageTk.PhotoImage(img) for img in pil_images]
                self._results[idx] = {
                    "path": path,
                    "name": filename,
                    "thumbs": thumbs,
                    "thumb": thumbs[self._thumb_size_idx],
                }
            except Exception:
                # エラー時はプレースホルダー
                placeholder = [
                    ImageTk.PhotoImage(Image.new("RGB", (s, s), (80, 80, 80)))
                    for s in THUMB_SIZES
                ]
                self._results[idx] = {
                    "path": "",
                    "name": "error",
                    "thumbs": placeholder,
                    "thumb": placeholder[self._thumb_size_idx],
                }
            self._completed_count += 1

        if batch:
            self._draw_progress(self._completed_count, self._total_count)

        # 全完了チェック
        if self._completed_count >= self._total_count:
            self.images = [r for r in self._results if r is not None]
            self._results = None
            self.btn_rename.config(state=tk.NORMAL if self.images else tk.DISABLED)
            self._finish_loading()
            self._draw_grid()
            return

        # 次のポーリング
        self.root.after(POLL_INTERVAL_MS, self._poll_futures)

    def _draw_progress(self, current, total):
        self.canvas.delete("all")
        cw = self.canvas.winfo_width()
        ch = self.canvas.winfo_height()
        if cw < 10 or ch < 10:
            return

        bar_w = min(300, cw - 60)
        bar_h = 24
        bx = (cw - bar_w) // 2
        by = ch // 2 - bar_h // 2

        # 背景バー
        self.canvas.create_rectangle(bx, by, bx + bar_w, by + bar_h,
                                     fill="#444444", outline="#666666")
        # 進捗バー
        if total > 0:
            ratio = current / total
            fill_w = int(bar_w * ratio)
            if fill_w > 0:
                self.canvas.create_rectangle(bx, by, bx + fill_w, by + bar_h,
                                             fill="#00bfff", outline="")

        # パーセント表示
        pct = int(current / total * 100) if total > 0 else 0
        self.canvas.create_text(cw // 2, by + bar_h + 16,
                                text=f"{current}/{total} ({pct}%)",
                                fill="white", font=("Consolas", 10))

    # ── Grid drawing ────────────────────────────────────────

    def _calc_columns(self, canvas=None):
        if canvas is None:
            canvas = self.canvas
        w = canvas.winfo_width()
        cell = self._thumb_size + CELL_PADDING * 2
        return max(1, w // cell)

    def _draw_grid(self):
        for c in self._visible_canvases():
            self._draw_grid_on(c)

    def _draw_grid_on(self, canvas):
        canvas.delete("all")
        if not self.images:
            canvas.config(scrollregion=(0, 0, 0, 0))
            return

        ts = self._thumb_size
        cols = self._calc_columns(canvas)
        cell_w = ts + CELL_PADDING * 2
        cell_h = ts + CELL_PADDING * 2 + LABEL_HEIGHT
        show_marker = (canvas is self._active_canvas) or not self._split_mode

        for i, item in enumerate(self.images):
            row, col = divmod(i, cols)
            x = col * cell_w + CELL_PADDING + ts // 2
            y = row * cell_h + CELL_PADDING + ts // 2

            tag_prefix = "L" if canvas is self.canvas else "R"
            canvas.create_image(x, y, image=item["thumb"],
                                tags=(f"{tag_prefix}_img_{i}", "thumb"))
            canvas.create_text(
                x, y + ts // 2 + 4,
                text=item["name"], fill="white", font=("Consolas", 9),
                tags=(f"{tag_prefix}_lbl_{i}", "label"),
            )

            # Draw insert marker if dragging
            if show_marker and self.insert_index is not None and i == self.insert_index and i != self.drag_index:
                mx = col * cell_w + 1
                my = row * cell_h + CELL_PADDING
                canvas.create_line(
                    mx, my, mx, my + ts,
                    fill="#00bfff", width=3, tags="marker",
                )

        # Insert marker at end
        if show_marker and self.insert_index is not None and self.insert_index == len(self.images):
            i_end = len(self.images)
            row, col = divmod(i_end, cols)
            mx = col * cell_w + 1
            my = row * cell_h + CELL_PADDING
            canvas.create_line(
                mx, my, mx, my + ts,
                fill="#00bfff", width=3, tags="marker",
            )

        total_rows = (len(self.images) + cols - 1) // cols
        total_h = total_rows * cell_h + CELL_PADDING
        canvas.config(scrollregion=(0, 0, cols * cell_w, total_h))

    def _on_canvas_resize(self, event):
        if not self._loading:
            self._draw_grid()

    def _on_mousewheel(self, event, canvas=None):
        if canvas is None:
            canvas = self.canvas
        if event.state & 0x4:  # Ctrl held
            return
        canvas.yview_scroll(-1 * (event.delta // 120), "units")

    def _on_ctrl_mousewheel(self, event):
        if self._loading or not self.images:
            return
        if event.delta > 0:
            self._zoom_in()
        else:
            self._zoom_out()

    def _change_thumb_size(self, new_idx):
        if new_idx == self._thumb_size_idx:
            return
        self._thumb_size_idx = new_idx
        for item in self.images:
            item["thumb"] = item["thumbs"][self._thumb_size_idx]
        self._draw_grid()

    def _zoom_in(self):
        if self._loading or not self.images:
            return
        self._change_thumb_size(min(self._thumb_size_idx + 1, len(THUMB_SIZES) - 1))

    def _zoom_out(self):
        if self._loading or not self.images:
            return
        self._change_thumb_size(max(self._thumb_size_idx - 1, 0))

    # ── Drag & Drop ─────────────────────────────────────────

    def _hit_index(self, canvas, x, y):
        """canvas座標からグリッドインデックスを返す"""
        ts = self._thumb_size
        cols = self._calc_columns(canvas)
        cell_w = ts + CELL_PADDING * 2
        cell_h = ts + CELL_PADDING * 2 + LABEL_HEIGHT

        col = int(x // cell_w)
        row = int(y // cell_h)
        idx = row * cols + col

        if 0 <= idx < len(self.images):
            return idx
        return None

    def _insert_position(self, canvas, x, y):
        """ドロップ位置から挿入インデックスを算出"""
        ts = self._thumb_size
        cols = self._calc_columns(canvas)
        cell_w = ts + CELL_PADDING * 2
        cell_h = ts + CELL_PADDING * 2 + LABEL_HEIGHT

        col_f = x / cell_w
        row = int(y // cell_h)
        col = int(col_f)

        # セルの右半分なら次のインデックスに挿入
        frac = col_f - col
        idx = row * cols + col
        if frac > 0.5:
            idx += 1

        return max(0, min(idx, len(self.images)))

    def _get_canvas_at(self, x_root, y_root):
        """スクリーン座標からマウス下のキャンバスを返す"""
        for c in self._visible_canvases():
            cx = c.winfo_rootx()
            cy = c.winfo_rooty()
            cw = c.winfo_width()
            ch = c.winfo_height()
            if cx <= x_root < cx + cw and cy <= y_root < cy + ch:
                return c
        return None

    def _screen_to_canvas_coords(self, canvas, x_root, y_root):
        """スクリーン座標をキャンバスのスクロール補正済み座標に変換"""
        local_x = x_root - canvas.winfo_rootx()
        local_y = y_root - canvas.winfo_rooty()
        return canvas.canvasx(local_x), canvas.canvasy(local_y)

    def _on_press(self, event, canvas=None):
        if canvas is None:
            canvas = self.canvas
        if not self.images or self._loading:
            return
        cx = canvas.canvasx(event.x)
        cy = canvas.canvasy(event.y)
        idx = self._hit_index(canvas, cx, cy)
        if idx is not None:
            self.drag_index = idx
            self._drag_canvas = canvas
            self._active_canvas = canvas
            # Create ghost overlay
            item = self.images[idx]
            self.drag_ghost = canvas.create_image(
                cx, cy, image=item["thumb"], tags="ghost"
            )
            canvas.itemconfigure(self.drag_ghost, state=tk.NORMAL)
            # Dim the original
            tag_prefix = "L" if canvas is self.canvas else "R"
            canvas.itemconfigure(f"{tag_prefix}_img_{idx}", state=tk.HIDDEN)

    def _on_drag(self, event):
        if self.drag_index is None:
            return

        # イベントはドラッグ開始キャンバスに届くが、マウスは別キャンバス上の可能性がある
        current_canvas = self._get_canvas_at(event.x_root, event.y_root)
        if current_canvas is None:
            current_canvas = self._active_canvas or self._drag_canvas

        cx, cy = self._screen_to_canvas_coords(current_canvas, event.x_root, event.y_root)

        # キャンバスが変わった場合、ゴーストを移動先に再生成
        if current_canvas is not self._active_canvas:
            # 旧キャンバスのゴーストを削除
            if self._active_canvas and self.drag_ghost:
                self._active_canvas.delete("ghost")
            self._active_canvas = current_canvas
            # 新キャンバスにゴーストを再生成
            item = self.images[self.drag_index]
            self.drag_ghost = current_canvas.create_image(
                cx, cy, image=item["thumb"], tags="ghost"
            )

        # Move ghost
        if self.drag_ghost:
            current_canvas.coords(self.drag_ghost, cx, cy)

        # Update insert marker
        new_insert = self._insert_position(current_canvas, cx, cy)
        if new_insert != self.insert_index:
            self.insert_index = new_insert
            self._draw_grid()
            # Re-create ghost on top after redraw
            item = self.images[self.drag_index]
            self.drag_ghost = current_canvas.create_image(
                cx, cy, image=item["thumb"], tags="ghost"
            )

        # 自動スクロール判定
        local_y = event.y_root - current_canvas.winfo_rooty()
        self._check_auto_scroll(current_canvas, local_y)

    def _check_auto_scroll(self, canvas, widget_y):
        """ウィンドウ座標でエッジ判定し、自動スクロールを開始/停止"""
        canvas_h = canvas.winfo_height()

        if widget_y < AUTO_SCROLL_ZONE:
            # 上端付近 → 上方向スクロール
            distance = max(1, AUTO_SCROLL_ZONE - widget_y)
            self._scroll_direction = -1
            self._scroll_speed = 1 + distance // 15
        elif widget_y > canvas_h - AUTO_SCROLL_ZONE:
            # 下端付近 → 下方向スクロール
            distance = max(1, widget_y - (canvas_h - AUTO_SCROLL_ZONE))
            self._scroll_direction = 1
            self._scroll_speed = 1 + distance // 15
        else:
            self._cancel_auto_scroll()
            return

        # タイマーが未起動なら開始
        if self._auto_scroll_after_id is None:
            self._auto_scroll_tick()

    def _auto_scroll_tick(self):
        """タイマーによる連続スクロール"""
        if self.drag_index is None:
            self._cancel_auto_scroll()
            return

        canvas = self._active_canvas or self.canvas
        canvas.yview_scroll(self._scroll_direction * self._scroll_speed, "units")
        self._auto_scroll_after_id = self.root.after(
            AUTO_SCROLL_INTERVAL, self._auto_scroll_tick
        )

    def _cancel_auto_scroll(self):
        if self._auto_scroll_after_id is not None:
            self.root.after_cancel(self._auto_scroll_after_id)
            self._auto_scroll_after_id = None

    def _on_drop(self, event):
        self._cancel_auto_scroll()

        if self.drag_index is None:
            self.insert_index = None
            return

        if self.insert_index is not None:
            src = self.drag_index
            dst = self.insert_index
            if dst != src and dst != src + 1:
                item = self.images.pop(src)
                if dst > src:
                    dst -= 1
                self.images.insert(dst, item)

        self.drag_index = None
        self.insert_index = None
        self.drag_ghost = None
        self._active_canvas = None
        self._drag_canvas = None
        self._draw_grid()

    # ── Image Viewer ─────────────────────────────────────────

    def _on_double_click(self, event, canvas=None):
        if canvas is None:
            canvas = self.canvas
        if not self.images or self._loading:
            return
        cx = canvas.canvasx(event.x)
        cy = canvas.canvasy(event.y)
        idx = self._hit_index(canvas, cx, cy)
        if idx is not None:
            self._open_viewer(idx)

    def _open_viewer(self, index):
        # 既存ビューアがあれば閉じる
        if self._viewer_win is not None:
            try:
                self._viewer_win.destroy()
            except Exception:
                pass

        self._viewer_index = index
        win = tk.Toplevel(self.root)
        win.title("PixSort — ビューア")
        win.configure(bg="#000000")
        self._viewer_win = win
        self._viewer_photo = None  # 参照保持用

        self._viewer_canvas = tk.Canvas(win, bg="#000000", highlightthickness=0)
        self._viewer_canvas.pack(fill=tk.BOTH, expand=True)

        win.bind("<Key>", self._viewer_on_key)
        win.protocol("WM_DELETE_WINDOW", self._close_viewer)
        win.focus_set()

        self._viewer_show_image(index)

    def _viewer_show_image(self, index):
        if not (0 <= index < len(self.images)):
            return
        self._viewer_index = index
        path = self.images[index]["path"]

        try:
            img = Image.open(path)
        except Exception:
            return

        # 画面サイズに収まるようリサイズ
        screen_w = self.root.winfo_screenwidth() - 80
        screen_h = self.root.winfo_screenheight() - 120
        img_w, img_h = img.size

        if img_w > screen_w or img_h > screen_h:
            ratio = min(screen_w / img_w, screen_h / img_h)
            new_w = int(img_w * ratio)
            new_h = int(img_h * ratio)
            img = img.resize((new_w, new_h), Image.LANCZOS)
        else:
            new_w, new_h = img_w, img_h

        self._viewer_photo = ImageTk.PhotoImage(img)

        win = self._viewer_win
        win.geometry(f"{new_w}x{new_h}")
        win.title(f"PixSort — {self.images[index]['name']}")

        self._viewer_canvas.delete("all")
        self._viewer_canvas.create_image(
            new_w // 2, new_h // 2, image=self._viewer_photo
        )

    def _viewer_on_key(self, event):
        if event.keysym == "Escape":
            self._close_viewer()
        elif event.keysym == "Left":
            if self._viewer_index > 0:
                self._viewer_show_image(self._viewer_index - 1)
        elif event.keysym == "Right":
            if self._viewer_index < len(self.images) - 1:
                self._viewer_show_image(self._viewer_index + 1)

    def _close_viewer(self):
        if self._viewer_win is not None:
            self._viewer_win.destroy()
            self._viewer_win = None
            self._viewer_photo = None

    # ── Rename ──────────────────────────────────────────────

    def _do_rename(self):
        if not self.images:
            return

        count = len(self.images)
        max_num = count * 10
        if max_num < 1000:
            digits = 3
        else:
            digits = len(str(max_num))

        # Confirm
        msg = f"{count} 個の画像を連番({str(10).zfill(digits)}, {str(20).zfill(digits)}, ...)でリネームするのだ。\n実行する？"
        if not messagebox.askyesno("確認", msg):
            return

        # Phase 1: rename to temp names
        temp_map = []
        for i, item in enumerate(self.images):
            old = item["path"]
            temp_name = f"__temp_{i:06d}.png"
            temp_path = os.path.join(self.directory, temp_name)
            os.rename(old, temp_path)
            temp_map.append(temp_path)

        # Phase 2: rename to final names
        for i, temp_path in enumerate(temp_map):
            num = (i + 1) * 10
            new_name = f"{str(num).zfill(digits)}.png"
            new_path = os.path.join(self.directory, new_name)
            os.rename(temp_path, new_path)
            self.images[i]["path"] = new_path
            self.images[i]["name"] = new_name

        self._draw_grid()
        messagebox.showinfo("完了", f"{count} 個のファイルをリネームしたのだ。")


def main():
    root = TkinterDnD.Tk()
    ImageSorterApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
